// TODO: a lot of the ints here can overflow and should be guarded from that

use std::{
    collections::BTreeMap,
    convert::TryFrom,
    str::{Chars, FromStr},
};

#[derive(Debug)]
pub struct Error;

type Result<T> = std::result::Result<T, Error>;

pub fn parse(s: &str) -> Result<BTreeMap<String, Value>> {
    let mut chars = CharIt::new(s);

    // > The top-level table, also called the root table, starts at the beginning of the document
    // > and ends just before the first table header (or EOF). Unlike other tables, it is nameless
    // > and cannot be relocated.
    let mut root_table = Table::new(Def::Implicit, Kind::Multiline);
    parse_pairs(&mut chars, &mut root_table)?;

    while chars.peek() == Some('[') {
        match chars.peek_n() {
            [Some('['), Some('[')] => parse_table_array_push(&mut chars, &mut root_table)?,
            [Some('['), _] => parse_table(&mut chars, &mut root_table)?,
            _ => unreachable!(),
        }
    }

    if chars.peek().is_none() {
        if let Value::Table(t) = Value::from(Ir::Table(root_table)) {
            Ok(t)
        } else {
            unreachable!();
        }
    } else {
        todo!("Lingering bytes");
    }
}

#[derive(Debug, PartialEq)]
pub enum Def {
    Implicit,
    Explicit,
}

#[derive(Debug, PartialEq)]
pub enum Kind {
    Inline,
    Multiline,
}

#[derive(Debug, PartialEq)]
pub struct Table {
    pub inner: BTreeMap<String, Ir>,
    pub def: Def,
    pub kind: Kind,
}

impl Table {
    fn new(def: Def, kind: Kind) -> Self {
        Self {
            inner: BTreeMap::new(),
            def,
            kind,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    Array(Vec<Value>),
    Table(BTreeMap<String, Value>),
    Datetime(Datetime),
}

impl From<Ir> for Value {
    fn from(ir: Ir) -> Self {
        match ir {
            Ir::Boolean(b) => Self::Boolean(b),
            Ir::Integer(i) => Self::Integer(i),
            Ir::Float(f) => Self::Float(f),
            Ir::String(s) => Self::String(s),
            Ir::Array(arr) => Self::Array(arr.into_iter().map(Self::from).collect()),
            Ir::Table(t) => {
                let t = t
                    .inner
                    .into_iter()
                    .map(|(k, v)| (k, Self::from(v)))
                    .collect();
                Self::Table(t)
            }
            Ir::Datetime(dt) => Self::Datetime(dt),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Ir {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    Array(Vec<Ir>),
    Table(Table),
    Datetime(Datetime),
}

impl TryFrom<u64> for Ir {
    type Error = Error;

    fn try_from(value: u64) -> Result<Self> {
        let int = i64::try_from(value).map_err(|_| Error)?;
        Ok(Self::from(int))
    }
}

impl From<i64> for Ir {
    fn from(int: i64) -> Self {
        Self::Integer(int)
    }
}

impl From<f64> for Ir {
    fn from(float: f64) -> Self {
        Self::Float(float)
    }
}

#[derive(Clone)]
struct CharIt<'a>(Chars<'a>);

impl<'a> CharIt<'a> {
    fn new(s: &'a str) -> Self {
        Self(s.chars())
    }

    #[must_use]
    fn ensure_next(&mut self, c: char) -> bool {
        self.next() == Some(c)
    }

    #[must_use]
    fn ensure_next_n<const N: usize>(&mut self, ensure: [char; N]) -> bool {
        ensure
            .iter()
            .all(|&ensure_elem| self.next() == Some(ensure_elem))
    }

    fn peek(&self) -> Option<char> {
        let mut lookahead = self.0.clone();
        lookahead.next()
    }

    #[must_use]
    fn peek_n<const N: usize>(&self) -> [Option<char>; N] {
        let mut lookahead = self.clone();
        lookahead.next_n()
    }

    #[must_use]
    fn next_n<const N: usize>(&mut self) -> [Option<char>; N] {
        let mut arr = [None; N];
        for elem in arr.iter_mut() {
            *elem = self.next();
        }
        arr
    }

    #[must_use]
    fn next_if_eq(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.unwrap_next();
            true
        } else {
            false
        }
    }

    #[must_use]
    fn next_n_some_or<const N: usize>(&mut self, err: Error) -> Result<[char; N]> {
        let mut arr = ['\0'; N];
        for elem in arr.iter_mut() {
            match self.next() {
                Some(c) => *elem = c,
                None => return Err(err),
            }
        }

        Ok(arr)
    }

    fn unwrap_next(&mut self) -> char {
        self.next().unwrap()
    }

    fn unwrap_next_n<const N: usize>(&mut self) -> [char; N] {
        let mut arr = ['\0'; N];
        for elem in arr.iter_mut() {
            *elem = self.next().unwrap();
        }
        arr
    }
}

impl Iterator for CharIt<'_> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

fn eat_comments_whitespace_and_newlines(chars: &mut CharIt<'_>) -> Result<bool> {
    let mut ate = false;
    while eat_whitespace_and_newlines(chars) || eat_comments(chars)? {
        ate = true;
    }

    Ok(ate)
}

fn eat_comments_and_whitespace(chars: &mut CharIt<'_>) -> Result<bool> {
    let mut ate = false;
    while eat_comments(chars)? || eat_whitespace(chars) {
        ate = true;
    }

    Ok(ate)
}

fn eat_whitespace_and_newlines(chars: &mut CharIt<'_>) -> bool {
    let mut ate = false;
    while eat_whitespace(chars) || eat_newlines(chars) {
        ate = true;
    }

    ate
}

fn eat_whitespace(chars: &mut CharIt<'_>) -> bool {
    let mut ate = false;
    loop {
        match chars.peek() {
            Some('\t') | Some(' ') => {
                chars.unwrap_next();
                ate = true;
            }
            _ => break,
        }
    }

    ate
}

fn eat_newlines_or_eof(chars: &mut CharIt<'_>) -> bool {
    eat_newlines(chars) || chars.peek().is_none()
}

fn eat_newlines(chars: &mut CharIt<'_>) -> bool {
    let mut ate = false;
    loop {
        match chars.peek_n() {
            [Some('\n'), _] => {
                chars.unwrap_next();
                ate = true;
            }
            [Some('\r'), Some('\n')] => {
                chars.unwrap_next_n::<2>();
                ate = true;
            }
            _ => break,
        }
    }

    ate
}

/// > A hash symbol marks the rest of the line as a comment, except when inside a string.
///
/// > Control characters other than tab (U+0000 to U+0008, U+000A to U+001F, U+007F) are not
/// > permitted in comments.
fn eat_comments(chars: &mut CharIt<'_>) -> Result<bool> {
    if chars.peek() != Some('#') {
        Ok(false)
    } else {
        chars.unwrap_next();
        loop {
            match chars.peek() {
                Some('\r') => {
                    chars.unwrap_next();
                    match chars.next() {
                        Some('\n') => break,
                        _ => return Err(Error),
                    }
                }
                None | Some('\n') => break,
                // Quoted control codes
                Some('\u{00}'..='\u{08}' | '\u{0A}'..='\u{1F}' | '\u{7F}') => return Err(Error),
                _ => {
                    let _ = chars.unwrap_next();
                }
            }
        }

        Ok(true)
    }
}

fn parse_pairs(chars: &mut CharIt<'_>, us: &mut Table) -> Result<()> {
    loop {
        eat_comments_whitespace_and_newlines(chars)?;

        if parse_maybe_pair(chars, us)?.is_none() {
            break Ok(());
        }

        eat_comments_and_whitespace(chars)?;

        if !eat_newlines_or_eof(chars) {
            break Err(Error);
        }
    }
}

fn parse_maybe_pair(chars: &mut CharIt<'_>, parent: &mut Table) -> Result<Option<()>> {
    let (key, cont) = if let Some((key, cont)) = parse_maybe_key(chars)? {
        (key, cont)
    } else {
        return Ok(None);
    };
    match cont {
        FigureOutTheLifetimes::More => {
            let us = parent
                .inner
                .entry(key)
                .or_insert_with(|| Ir::Table(Table::new(Def::Implicit, Kind::Multiline)));
            match us {
                Ir::Table(
                    us @ Table {
                        kind: Kind::Multiline,
                        ..
                    },
                ) => parse_maybe_pair(chars, us),
                _ => return Err(Error),
            }
        }
        FigureOutTheLifetimes::Fini => {
            if !chars.ensure_next('=') {
                return Err(Error);
            }

            eat_whitespace(chars);

            let value = parse_value(chars)?;

            if parent.inner.get(&key).is_some() {
                return Err(Error);
            }

            parent.inner.insert(key, value);

            Ok(Some(()))
        }
    }
}

#[derive(Debug)]
enum FigureOutTheLifetimes {
    More,
    Fini,
}

// TODO: What is valid for the starting character of a bare key. Surely `-` isn't, but what else?
// TODO: add a new toml-test test for ^^
// TODO: add a test for multiline strings being used as keys
fn parse_maybe_key(chars: &mut CharIt<'_>) -> Result<Option<(String, FigureOutTheLifetimes)>> {
    // > A key may either be bare, quoted, or dotted.
    let segment = match chars.peek() {
        // > **Bare keys** may only contain ASCII letters, ASCII digits, underscores, and dashes
        // > (`A-Za-z0-9_-`). Note that bare keys are allowed to be composed of only ASCII digits,
        // > e.g. `1234`, but are always interpreted as strings.
        Some('A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '-') => {
            let mut key = String::from(chars.unwrap_next());
            loop {
                if let Some('A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '-') = chars.peek() {
                    key.push(chars.unwrap_next());
                } else {
                    break;
                }
            }
            Ok(Some(key))
        }
        // > **Quoted keys** follow the exact same rules as either basic strings or literal strings
        // > and allow you to use a much broader set of key names. Best practice is to use bare keys
        // > except when absolutely necessary.
        Some('"') => parse_basic_string(chars).map(Some),
        Some('\'') => parse_literal_string(chars).map(Some),
        // Table or nothing instead of a key
        Some('[') | None => Ok(None),
        _ => Err(Error),
    };

    eat_whitespace(chars);

    let cont = if chars.next_if_eq('.') {
        eat_whitespace(chars);
        FigureOutTheLifetimes::More
    } else {
        FigureOutTheLifetimes::Fini
    };

    segment.map(|maybe| maybe.map(|s| (s, cont)))
}

fn parse_value(chars: &mut CharIt<'_>) -> Result<Ir> {
    match chars.peek() {
        Some('t' | 'f') => {
            let b = parse_bool(chars)?;
            Ok(Ir::Boolean(b))
        }
        Some('+' | '-' | '0'..='9' | 'i' | 'n') => match chars.peek_n() {
            [_, _, Some(':'), _, _] | [_, _, _, _, Some('-')] => {
                let dt = parse_datetime(chars)?;
                Ok(Ir::Datetime(dt))
            }
            _ => parse_number(chars),
        },
        Some('\'' | '"') => {
            let s = parse_string(chars)?;
            Ok(Ir::String(s))
        }
        Some('[') => {
            let arr = parse_array(chars)?;
            Ok(Ir::Array(arr))
        }
        Some('{') => {
            let table = parse_inline_table(chars)?;
            Ok(Ir::Table(table))
        }
        _ => Err(Error),
    }
}

/// > Booleans are just the tokens you're used to. Always lowercase.
fn parse_bool(chars: &mut CharIt<'_>) -> Result<bool> {
    match chars.next_n_some_or(Error)? {
        ['t', 'r', 'u', 'e'] => Ok(true),
        ['f', 'a', 'l', 's'] if chars.ensure_next('e') => Ok(false),
        _ => Err(Error),
    }
}

fn parse_number(chars: &mut CharIt<'_>) -> Result<Ir> {
    match chars.peek_n() {
        // > Non-negative integer values may also be expressed in hexadecimal, octal, or binary. In
        // > these formats, leading `+` is not allowed and leading zeros are allowed (after the
        // > prefix). Hex values are case-insensitive. Underscores are allowed between digits (but
        // > not between the prefix and the value).
        [Some('0'), Some('x')] => parse_hexadecimal_number(chars).and_then(Ir::try_from),
        [Some('0'), Some('o')] => parse_octal_number(chars).and_then(Ir::try_from),
        [Some('0'), Some('b')] => parse_binary_number(chars).and_then(Ir::try_from),
        // (+|-)(inf|nan)
        [Some('+' | '-'), Some('i' | 'n')] | [Some('i' | 'n'), _] => {
            parse_float(chars).map(Ir::from)
        }
        _ => {
            // Look ahead for a `.`, `e`, or `E` to indicate if this is a float
            let is_float = chars
                .clone()
                .take_while(|c| matches!(c, '0'..='9' | '_' | '-' | '+' | '.' | 'e' | 'E'))
                .find(|c| ['.', 'e', 'E'].contains(&c))
                .is_some();

            if is_float {
                parse_float(chars).map(Ir::from)
            } else {
                parse_int(chars).map(Ir::from)
            }
        }
    }
}

fn parse_binary_number(chars: &mut CharIt<'_>) -> Result<u64> {
    parse_generic_prefixed_number(maybe_bit_char_to_u8, 2, chars)
}

fn parse_octal_number(chars: &mut CharIt<'_>) -> Result<u64> {
    parse_generic_prefixed_number(maybe_octal_char_to_u8, 8, chars)
}

fn parse_hexadecimal_number(chars: &mut CharIt<'_>) -> Result<u64> {
    parse_generic_prefixed_number(maybe_hex_char_to_u8, 16, chars)
}

fn parse_generic_prefixed_number(
    parse_digit_fn: fn(Option<char>) -> Option<u8>,
    radix: u8,
    chars: &mut CharIt<'_>,
) -> Result<u64> {
    // Pop off the prefix
    chars.unwrap_next_n::<2>();
    parse_generic_number(parse_digit_fn, radix, chars)
}

#[derive(PartialEq)]
enum DigitOrUnderscore {
    Digit,
    Underscore,
}

fn parse_generic_number(
    parse_digit_fn: fn(Option<char>) -> Option<u8>,
    radix: u8,
    chars: &mut CharIt<'_>,
) -> Result<u64> {
    let mut acc = 0;

    // > Underscores are allowed between digits (but not between the prefix and the value).
    let digit = parse_digit_fn(chars.peek()).ok_or(Error)?;
    chars.unwrap_next();
    acc += u64::from(digit);

    // > For large numbers, you may use underscores between digits to enhance readability. Each
    // > underscore must be surrounded by at least one digit on each side.
    // We just parsed a single digit
    let mut lookbehind_1 = DigitOrUnderscore::Digit;
    loop {
        let c = chars.peek();
        if let Some(digit) = parse_digit_fn(c) {
            lookbehind_1 = DigitOrUnderscore::Digit;
            acc *= u64::from(radix);
            acc += u64::from(digit);
        } else if c == Some('_') {
            if lookbehind_1 == DigitOrUnderscore::Underscore {
                return Err(Error);
            }

            lookbehind_1 = DigitOrUnderscore::Underscore;
        } else {
            break;
        }
        chars.unwrap_next();
    }

    match lookbehind_1 {
        DigitOrUnderscore::Digit => Ok(acc),
        DigitOrUnderscore::Underscore => Err(Error),
    }
}

fn maybe_bit_char_to_u8(digit: Option<char>) -> Option<u8> {
    let b = u8::try_from(u32::from(digit?)).ok()?;
    match b {
        b'0' => Some(0),
        b'1' => Some(1),
        _ => None,
    }
}

fn maybe_octal_char_to_u8(digit: Option<char>) -> Option<u8> {
    let b = u8::try_from(u32::from(digit?)).ok()?;
    match b {
        b'0'..=b'7' => Some(b - b'0'),
        _ => None,
    }
}

fn maybe_hex_char_to_u8(digit: Option<char>) -> Option<u8> {
    let b = u8::try_from(u32::from(digit?)).ok()?;
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 0xa),
        b'A'..=b'F' => Some(b - b'A' + 0xa),
        _ => None,
    }
}

/// > Floats should be implemented as IEEE 754 binary64 values.
/// >
/// > A float consists of an integer part (which follows the same rules as decimal integer values)
/// > followed by a fractional part and/or an exponent part. If both a fractional part and exponent
/// > part are present, the fractional part must precede the exponent part.
// TODO: is there a lower effort way to handle float parsing here?
fn parse_float(chars: &mut CharIt<'_>) -> Result<f64> {
    let sign = parse_number_sign(chars).unwrap_or(Sign::Positive);

    match chars.peek_n() {
        // > Special float values can also be expressed. They are always lowercase.
        [Some('i'), Some('n'), Some('f')] => {
            chars.unwrap_next_n::<3>();
            Ok(match sign {
                Sign::Positive => f64::INFINITY,
                Sign::Negative => f64::NEG_INFINITY,
            })
        }
        // > Special float values can also be expressed. They are always lowercase.
        [Some('n'), Some('a'), Some('n')] => {
            chars.unwrap_next_n::<3>();
            Ok(match sign {
                Sign::Positive => f64::NAN,
                Sign::Negative => -f64::NAN,
            })
        }
        // TODO: this whole arm has a ton of duplicated logic
        [Some('0'..='9'), _, _] => {
            // TODO: Don't love that we allocate here, but float parsing is complicated
            let mut s = String::new();
            let mut lookbehind_1 = DigitOrUnderscore::Digit;
            while let Some(c) = chars.peek() {
                match c {
                    '0'..='9' => {
                        chars.unwrap_next();
                        lookbehind_1 = DigitOrUnderscore::Digit;
                        s.push(c);

                        // TODO: this  check should not be in this loop (add to toml test)
                        // No leading zeros allowed
                        if c == '0' && matches!(chars.peek(), Some('0'..='9')) {
                            return Err(Error);
                        }
                    }
                    '_' => {
                        chars.unwrap_next();
                        if lookbehind_1 == DigitOrUnderscore::Underscore {
                            return Err(Error);
                        }
                        lookbehind_1 = DigitOrUnderscore::Underscore;
                    }
                    '.' | 'e' | 'E' => break,
                    _ => return Err(Error),
                }
            }

            if lookbehind_1 == DigitOrUnderscore::Underscore {
                return Err(Error);
            }

            // TODO: are trailing zeros allowed?
            // > If both a fractional part and exponent part are present, the fractional part must
            // > precede the exponent part.
            if chars.next_if_eq('.') {
                // > A fractional part is a decimal point followed by one or more digits.
                s.push('.');
                if let Some(digit @ '0'..='9') = chars.next() {
                    s.push(digit);
                } else {
                    return Err(Error);
                }

                while let Some(c) = chars.peek() {
                    match c {
                        '0'..='9' => {
                            chars.unwrap_next();
                            lookbehind_1 = DigitOrUnderscore::Digit;
                            s.push(c);
                        }
                        '_' => {
                            chars.unwrap_next();
                            if lookbehind_1 == DigitOrUnderscore::Underscore {
                                return Err(Error);
                            }
                            lookbehind_1 = DigitOrUnderscore::Underscore;
                        }
                        _ => break,
                    }
                }

                if lookbehind_1 == DigitOrUnderscore::Underscore {
                    return Err(Error);
                }
            }

            // > An exponent part is an E (upper or lower case) followed by an integer part (which
            // > follows the same rules as decimal integer values but may include leading zeros).
            if let Some('e' | 'E') = chars.peek() {
                s.push(chars.unwrap_next());

                if let Some('+' | '-') = chars.peek() {
                    s.push(chars.unwrap_next());
                }

                if let Some(digit @ '0'..='9') = chars.next() {
                    s.push(digit);
                } else {
                    return Err(Error);
                }

                while let Some(c) = chars.peek() {
                    match c {
                        '0'..='9' => {
                            chars.unwrap_next();
                            lookbehind_1 = DigitOrUnderscore::Digit;
                            s.push(c);
                        }
                        '_' => {
                            chars.unwrap_next();
                            if lookbehind_1 == DigitOrUnderscore::Underscore {
                                return Err(Error);
                            }
                            lookbehind_1 = DigitOrUnderscore::Underscore;
                        }
                        _ => break,
                    }
                }

                if lookbehind_1 == DigitOrUnderscore::Underscore {
                    return Err(Error);
                }
            }

            let f: f64 = s.parse().unwrap();
            Ok(if sign == Sign::Positive { f } else { -f })
        }
        _ => Err(Error),
    }
}

#[derive(PartialEq)]
enum Sign {
    Positive,
    Negative,
}

fn parse_number_sign(chars: &mut CharIt<'_>) -> Option<Sign> {
    if chars.next_if_eq('+') {
        Some(Sign::Positive)
    } else if chars.next_if_eq('-') {
        Some(Sign::Negative)
    } else {
        None
    }
}

// TODO: is there a test for a leading zero followed by an underscore?
fn parse_int(chars: &mut CharIt<'_>) -> Result<i64> {
    let sign = parse_number_sign(chars).unwrap_or(Sign::Positive);

    // > Leading zeros are not allowed.
    if let [Some('0'), Some('_' | '0'..='9')] = chars.peek_n() {
        return Err(Error);
    }

    let unsigned = parse_generic_number(maybe_decimal_char_to_u8, 10, chars)?;

    // abs(i64::MIN) is one larger than i64::MAX which adds a single special case when doing a
    // checked conversion between i64 and u64 + sign
    if sign == Sign::Negative && unsigned == 1 + u64::try_from(i64::MAX).unwrap() {
        Ok(i64::MIN)
    } else {
        let mut signed = i64::try_from(unsigned).map_err(|_| Error)?;
        if sign == Sign::Negative {
            signed *= -1;
        }

        Ok(signed)
    }
}

fn maybe_decimal_char_to_u8(digit: Option<char>) -> Option<u8> {
    let b = u8::try_from(u32::from(digit?)).ok()?;
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        _ => None,
    }
}

#[derive(Debug, PartialEq)]
pub struct Datetime {
    pub date: Option<Date>,
    pub time: Option<Time>,
    pub offset: Option<Offset>,
}

impl FromStr for Datetime {
    type Err = Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        parse_datetime(&mut CharIt::new(s))
    }
}

#[derive(Debug, PartialEq)]
pub struct Date {
    pub year: u16,
    pub month: u8,
    pub day: u8,
}

impl Date {
    // TODO: max day depends on year and month?
    fn new(year: u16, month: u8, day: u8) -> Option<Self> {
        if (1..=12).contains(&month) && (1..=31).contains(&day) {
            Some(Self { year, month, day })
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Time {
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
    pub nanos: u32,
}

impl Time {
    fn new(hour: u8, minute: u8, second: u8, nanos: u32) -> Option<Self> {
        if (0..=23).contains(&hour)
            && (0..59).contains(&minute)
            && (0..59).contains(&second)
            && (0..1_000_000_000).contains(&nanos)
        {
            Some(Self {
                hour,
                minute,
                second,
                nanos,
            })
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Offset {
    Z,
    Custom { minutes: i16 },
}

impl Offset {
    fn custom(is_pos: bool, hour: u32, minute: u32) -> Option<Self> {
        // TODO: add test for minute over
        if (0..24).contains(&hour) && (0..60).contains(&minute) {
            let mut minutes = i16::try_from(minute).unwrap() + (i16::try_from(hour).unwrap() * 60);
            if !is_pos {
                minutes = -minutes;
            }

            Some(Self::Custom { minutes })
        } else {
            None
        }
    }
}

/// Parses a date-time
///
/// Can be represented as:
/// 1. Offset date-time per RFC 3339
/// 2. Local date-time (RFC 3339 with no offset)
/// 3. Local date (date portion of RFC 3339)
/// 4. Local time (time portion of RFC 3339)
// TODO: snapshot test with values from here to verify that returned data is correct
// TODO: split up logic for parsing date, time, and offset into separate functions that can be
//       called
fn parse_datetime(chars: &mut CharIt<'_>) -> Result<Datetime> {
    // TODO: consolidate logic with `parse_fixed_width_ascii_hex`
    fn parse_fixed_width_ascii_decimal<const N: usize>(arr: [char; N]) -> Result<u32> {
        arr.iter()
            .try_fold(0, |mut acc, &digit| {
                acc *= 10;
                acc += u32::from(maybe_decimal_char_to_u8(Some(digit))?);
                Some(acc)
            })
            .ok_or(Error)
    }

    let mut date = None;
    let mut time = None;
    let mut offset = None;

    // Try to parse a date
    let mut can_have_offset = false;
    let mut must_have_time = false;
    let mut can_have_time = true;
    if chars.clone().nth(4) == Some('-') {
        can_have_offset = true;

        let year = chars.next_n_some_or::<4>(Error)?;
        let year = parse_fixed_width_ascii_decimal(year)?;

        // Checked by if condition
        assert!(chars.ensure_next('-'));

        let month = chars.next_n_some_or::<2>(Error)?;
        let month = parse_fixed_width_ascii_decimal(month)?;

        if !chars.ensure_next('-') {
            return Err(Error);
        }

        let day = chars.next_n_some_or::<2>(Error)?;
        let day = parse_fixed_width_ascii_decimal(day)?;

        let year: u16 = u16::try_from(year).map_err(|_| Error)?;
        let month: u8 = u8::try_from(month).map_err(|_| Error)?;
        let day: u8 = u8::try_from(day).map_err(|_| Error)?;

        date = Some(Date::new(year, month, day).ok_or(Error)?);

        match chars.peek() {
            Some('t' | 'T') => {
                chars.unwrap_next();
                must_have_time = true;
            }
            // TODO: can this ever make things invalid? My guess is probably
            // TODO: add a test to `toml-test` to cover this case?
            Some(' ') => {
                chars.unwrap_next();
            }
            _ => {
                can_have_time = false;
            }
        }
    }

    // Try to parse a time
    // TODO: this conditional is cursed
    if can_have_time && (must_have_time || chars.clone().nth(2) == Some(':')) {
        let ascii_hour = chars.next_n_some_or::<2>(Error)?;
        let hour = parse_fixed_width_ascii_decimal(ascii_hour)?;

        // Checked by if condition
        assert!(chars.ensure_next(':'));

        let ascii_min = chars.next_n_some_or::<2>(Error)?;
        let min = parse_fixed_width_ascii_decimal(ascii_min)?;

        // Seconds are optional
        let mut sec = 0;
        let mut nanos = 0;
        if chars.next_if_eq(':') {
            let ascii_sec = chars.next_n_some_or::<2>(Error)?;
            sec = parse_fixed_width_ascii_decimal(ascii_sec)?;

            // Subsec is optional
            if chars.next_if_eq('.') {
                let mut acc = 0;
                let mut num_mag_adjustments: u32 = 9;

                loop {
                    match chars.peek() {
                        Some('0'..='9') => {
                            let digit = chars.unwrap_next();
                            acc *= 10;
                            acc += u32::from(digit) - u32::from('0');
                            num_mag_adjustments =
                                num_mag_adjustments.checked_sub(1).ok_or(Error)?;
                        }
                        _ => break,
                    }
                }

                for _ in 0..num_mag_adjustments {
                    acc *= 10;
                }

                nanos = acc;
            }
        }

        // Infallible due to bound from number of digits
        let hour: u8 = u8::try_from(hour).unwrap();
        let min: u8 = u8::try_from(min).unwrap();
        let sec: u8 = u8::try_from(sec).unwrap();

        time = Some(Time::new(hour, min, sec, nanos).ok_or(Error)?);
    }

    // Try to parse offset
    if can_have_offset {
        match chars.peek() {
            Some('z' | 'Z') => {
                chars.next();
                offset = Some(Offset::Z);
            }
            Some('+' | '-') => {
                let is_pos = chars.next().unwrap() == '+';

                let ascii_hour = chars.next_n_some_or::<2>(Error)?;
                let hour = parse_fixed_width_ascii_decimal(ascii_hour)?;

                if !chars.ensure_next(':') {
                    return Err(Error);
                }

                let ascii_min = chars.next_n_some_or::<2>(Error)?;
                let min = parse_fixed_width_ascii_decimal(ascii_min)?;

                offset = Some(Offset::custom(is_pos, hour, min).ok_or(Error)?);
            }
            _ => {}
        }
    }

    // TODO: validate that we either have a date or time
    Ok(Datetime { date, time, offset })
}

/// > There are four ways to express strings: basic, multi-line basic, literal, and multi-line
/// > literal. All strings must contain only valid UTF-8 characters.
fn parse_string(chars: &mut CharIt<'_>) -> Result<String> {
    match chars.peek_n() {
        [Some('"'), Some('"'), Some('"')] => parse_multi_line_basic_string(chars),
        [Some('\''), Some('\''), Some('\'')] => parse_multi_line_literal_string(chars),
        [Some('"'), _, _] => parse_basic_string(chars),
        [Some('\''), _, _] => parse_literal_string(chars),
        _ => panic!("Must call with a string"),
    }
}

/// > Basic strings are surrounded by quotation marks ("). Any Unicode character may be used except
/// > those that must be escaped: quotation mark, backslash, and the control characters other than
/// > tab (U+0000 to U+0008, U+000A to U+001F, U+007F).
fn parse_basic_string(chars: &mut CharIt<'_>) -> Result<String> {
    assert!(chars.ensure_next('"'));

    let mut s = String::new();

    loop {
        // Must have a closing `"`
        let c = chars.next().ok_or(Error)?;

        match c {
            '\\' => {
                let unescaped = parse_basic_string_escaped_char(chars)?;
                s.push(unescaped);
            }
            '"' => break,
            '\u{00}'..='\u{08}' | '\u{0A}'..='\u{1F}' | '\u{7F}' => return Err(Error),
            other => s.push(other),
        }
    }

    Ok(s)
}

/// > Multi-line basic strings are surrounded by three quotation marks on each side and allow
/// > newlines.
// TODO: how should things like
// ```toml
// s = """\ """
// ```
// be handled?
fn parse_multi_line_basic_string(chars: &mut CharIt<'_>) -> Result<String> {
    assert!(chars.ensure_next_n(['"', '"', '"']));

    // > A newline immediately following the opening delimiter will be trimmed. All other
    // > whitespace and newline characters remain intact.
    match chars.peek_n() {
        [Some('\n'), _] => {
            let _ = chars.unwrap_next();
        }
        [Some('\r'), Some('\n')] => {
            let _ = chars.unwrap_next_n::<2>();
        }
        _ => {}
    }

    let mut s = String::new();

    loop {
        // Must have a closing `"""`
        let c = chars.next().ok_or(Error)?;

        match c {
            '\\' => {
                // > For writing long strings without introducing extraneous whitespace, use a
                // > "line ending backslash". When the last non-whitespace character on a line is an
                // > unescaped `\`, it will be trimmed along with all whitespace (including
                // > newlines) up to the next non-whitespace character or closing delimiter. All of
                // > the escape sequences that are valid for basic strings are also valid for
                // > multi-line basic strings.
                match chars.peek().ok_or(Error)? {
                    c @ ('\r' | '\n' | '\t' | ' ') => {
                        let mut ate_newline = c == '\n';
                        loop {
                            let c = chars.peek().ok_or(Error)?;
                            match c {
                                '\r' | '\t' | ' ' => {
                                    let _ = chars.unwrap_next();
                                }
                                '\n' => {
                                    chars.unwrap_next();
                                    ate_newline = true;
                                }
                                _ => {
                                    if ate_newline {
                                        break;
                                    } else {
                                        return Err(Error);
                                    }
                                }
                            }
                        }
                    }
                    _ => {
                        let unescaped = parse_basic_string_escaped_char(chars)?;
                        s.push(unescaped);
                    }
                }
            }
            // > You can write a quotation mark, or two adjacent quotation marks, anywhere inside a
            // > multi-line basic string. They can also be written just inside the delimiters.
            '"' => match chars.peek_n() {
                [Some('"'), Some('"')] => {
                    chars.unwrap_next_n::<2>();
                    //
                    // Up to 2 single quotes can be up against the end delimiter
                    for _ in 0..2 {
                        if chars.next_if_eq('"') {
                            s.push('"');
                        }
                    }

                    break;
                }
                _ => s.push('"'),
            },
            // > Any Unicode character may be used except those that must be escaped: ... (U+0000 to
            // > U+0008, U+000B, U+000C, U+000E to U+001F, U+007F).
            '\u{00}'..='\u{08}' | '\u{0B}' | '\u{0C}' | '\u{0E}'..='\u{1F}' | '\u{7F}' => {
                return Err(Error)
            }
            other => s.push(other),
        }
    }

    Ok(s)
}

/// > For convenience, some popular characters have a compact escape sequence.
/// >
/// > ```text
/// > \b         - backspace       (U+0008)
/// > \t         - tab             (U+0009)
/// > \n         - linefeed        (U+000A)
/// > \f         - form feed       (U+000C)
/// > \r         - carriage return (U+000D)
/// > \"         - quote           (U+0022)
/// > \\         - backslash       (U+005C)
/// > \uXXXX     - unicode         (U+XXXX)
/// > \UXXXXXXXX - unicode         (U+XXXXXXXX)
/// > ```
/// >
/// > Any Unicode character may be escaped with the `\uXXXX` or `\UXXXXXXXX` forms. The escape codes
/// > must be valid Unicode scalar values.
/// >
/// > All other escape sequences not listed above are reserved; if they are used, TOML should
/// > produce an error.
fn parse_basic_string_escaped_char(chars: &mut CharIt<'_>) -> Result<char> {
    fn parse_fixed_width_ascii_hex<const N: usize>(arr: [char; N]) -> Result<u32> {
        arr.iter()
            .try_fold(0, |mut acc, &digit| {
                acc <<= 4;
                acc += u32::from(maybe_hex_char_to_u8(Some(digit))?);
                Some(acc)
            })
            .ok_or(Error)
    }

    let c = chars.next().ok_or(Error)?;

    let unescaped = match c {
        'b' => '\u{08}',
        't' => '\t',
        'n' => '\n',
        'f' => '\u{0c}',
        'r' => '\r',
        '"' => '"',
        '\\' => '\\',
        'u' => {
            let arr = chars.next_n_some_or::<4>(Error)?;
            let int = parse_fixed_width_ascii_hex(arr)?;
            char::try_from(int).map_err(|_| Error)?
        }
        'U' => {
            let arr = chars.next_n_some_or::<8>(Error)?;
            let int = parse_fixed_width_ascii_hex(arr)?;
            char::try_from(int).map_err(|_| Error)?
        }
        _ => return Err(Error),
    };

    Ok(unescaped)
}

/// > To help, TOML supports literal strings which do not allow escaping at all.
/// >
/// > Literal strings are surrounded by single quotes. Like basic strings, they must appear on a
/// > single line:
fn parse_literal_string(chars: &mut CharIt<'_>) -> Result<String> {
    assert!(chars.ensure_next('\''));

    let mut s = String::new();

    loop {
        // Must have a closing `'`
        let c = chars.next().ok_or(Error)?;

        match c {
            '\'' => break,
            '\u{00}'..='\u{08}' | '\u{0A}'..='\u{1F}' | '\u{7F}' => return Err(Error),
            other => s.push(other),
        }
    }

    Ok(s)
}

/// > Multi-line literal strings are surrounded by three single quotes on each side and allow
/// > newlines. Like literal strings, there is no escaping whatsoever.
fn parse_multi_line_literal_string(chars: &mut CharIt<'_>) -> Result<String> {
    assert!(chars.ensure_next_n(['\'', '\'', '\'']));

    let mut s = String::new();

    // > A newline immediately following the opening delimiter will be trimmed. All other
    // > whitespace and newline characters remain intact.
    match chars.peek_n() {
        [Some('\n'), _] => {
            let _ = chars.unwrap_next();
        }
        [Some('\r'), Some('\n')] => {
            let _ = chars.unwrap_next_n::<2>();
        }
        _ => {}
    }

    loop {
        // Must have a closing `'''`
        let c = chars.next().ok_or(Error)?;

        // > All other content between the delimiters is treated as-is without modification.
        match c {
            // > You can write 1 or 2 single quotes anywhere within a multi-line literal string,
            // > but sequences of three or more single quotes are not permitted.
            '\'' => match chars.peek_n() {
                [Some('\''), Some('\'')] => {
                    chars.unwrap_next_n::<2>();

                    // Up to 2 single quotes can be up against the end delimiter
                    for _ in 0..2 {
                        if chars.next_if_eq('\'') {
                            s.push('\'');
                        }
                    }

                    break;
                }
                _ => s.push('\''),
            },
            // > Control characters other than tab are not permitted in a literal string.
            '\u{00}'..='\u{08}' | '\u{0B}'..='\u{0C}' | '\u{0E}'..='\u{1F}' | '\u{7F}' => {
                return Err(Error)
            }
            other => s.push(other),
        }
    }

    Ok(s)
}

// TODO: is `[,]` valid?
fn parse_array(chars: &mut CharIt<'_>) -> Result<Vec<Ir>> {
    assert!(chars.ensure_next('['));

    let mut arr = Vec::new();
    let mut first = true;
    loop {
        eat_comments_whitespace_and_newlines(chars)?;

        if chars.next_if_eq(']') {
            break;
        }

        if !first {
            if !chars.ensure_next(',') {
                return Err(Error);
            }
            eat_comments_whitespace_and_newlines(chars)?;

            // Dangling comma is fine, but duplicate commas aren't
            if chars.next_if_eq(']') {
                break;
            }
        }
        first = false;

        let val = parse_value(chars)?;
        arr.push(val);
    }

    Ok(arr)
}

// TODO: test inline-table ending with no closing bracket
fn parse_inline_table(chars: &mut CharIt<'_>) -> Result<Table> {
    assert!(chars.ensure_next('{'));

    // TODO: newlines, comments?
    eat_whitespace(chars);

    let mut table = Table::new(Def::Explicit, Kind::Inline);

    if chars.next_if_eq('}') {
        return Ok(table);
    }

    loop {
        // TODO: newlines, comments?
        eat_whitespace(chars);

        if parse_maybe_pair(chars, &mut table)?.is_none() {
            return Err(Error);
        }

        // TODO: comments, newlines?
        eat_whitespace(chars);

        if chars.next_if_eq('}') {
            break;
        }

        if !chars.ensure_next(',') {
            return Err(Error);
        }
    }

    Ok(table)
}

/// > Tables (also known as hash tables or dictionaries) are collections of key/value pairs. They
/// > are defined by headers, with square brackets on a line by themselves. You can tell headers
/// > apart from arrays because arrays are only ever values.
/// >
/// > Under that, and until the next header or EOF, are the key/values of that table. Key/value
/// > pairs within tables are not guaranteed to be in any specific order.
fn parse_table(chars: &mut CharIt<'_>, parent: &mut Table) -> Result<()> {
    assert!(chars.ensure_next('['));
    parse_table_inner(chars, parent)
}

// TODO: > defining a super-table afterward is ok
// TODO: handle duplicate conflicts correctly
fn parse_table_inner(chars: &mut CharIt<'_>, parent: &mut Table) -> Result<()> {
    eat_whitespace(chars);

    // > Naming rules for tables are the same as for keys (see definition of Keys above).
    let (key, cont) = parse_maybe_key(chars)?.ok_or(Error)?;
    match cont {
        FigureOutTheLifetimes::More => {
            let us = parent
                .inner
                .entry(key)
                .or_insert_with(|| Ir::Table(Table::new(Def::Implicit, Kind::Multiline)));
            match us {
                Ir::Table(
                    child @ Table {
                        kind: Kind::Multiline,
                        ..
                    },
                ) => parse_table_inner(chars, child)?,
                _ => return Err(Error),
            }
        }
        FigureOutTheLifetimes::Fini => {
            if !chars.ensure_next(']') {
                return Err(Error);
            }

            let us = parent
                .inner
                .entry(key)
                .or_insert_with(|| Ir::Table(Table::new(Def::Implicit, Kind::Multiline)));
            match us {
                Ir::Table(
                    table @ Table {
                        def: Def::Implicit,
                        kind: Kind::Multiline,
                        ..
                    },
                ) => {
                    table.def = Def::Explicit;

                    eat_comments_and_whitespace(chars)?;

                    if !eat_newlines_or_eof(chars) {
                        return Err(Error);
                    }

                    parse_pairs(chars, table)?;
                }
                _ => return Err(Error),
            }
        }
    }

    Ok(())
}

// TODO: reference the spec here
fn parse_table_array_push(chars: &mut CharIt<'_>, parent: &mut Table) -> Result<()> {
    assert!(chars.ensure_next_n(['[', '[']));
    parse_table_array_push_inner(chars, parent)
}

// TODO: this is currently pretty broken and should be reworked
fn parse_table_array_push_inner(chars: &mut CharIt<'_>, parent: &mut Table) -> Result<()> {
    let (key, cont) = parse_maybe_key(chars)?.ok_or(Error)?;
    // TODO: this is done a bit strangely and should be reworked. Structure should always produce:
    // N * Table -> Array -> Table?
    match cont {
        FigureOutTheLifetimes::More => {
            let us = parent
                .inner
                .entry(key.clone())
                .or_insert_with(|| Ir::Table(Table::new(Def::Implicit, Kind::Multiline)));
            match us {
                Ir::Table(child) => parse_table_array_push_inner(chars, child)?,
                Ir::Array(arr) => {
                    // Revisit the same node
                    let us = arr.last_mut().unwrap();
                    match us {
                        Ir::Table(table) => parse_table_array_push_inner(chars, table)?,
                        _ => return Err(Error),
                    }
                }
                _ => return Err(Error),
            }
        }
        FigureOutTheLifetimes::Fini => {
            if !chars.ensure_next_n([']', ']']) {
                return Err(Error);
            }

            eat_comments_and_whitespace(chars)?;

            if !eat_newlines_or_eof(chars) {
                return Err(Error);
            }

            let us = parent
                .inner
                .entry(key)
                .or_insert_with(|| Ir::Array(Vec::new()));
            match us {
                Ir::Array(arr) => {
                    let mut entry = Table::new(Def::Explicit, Kind::Multiline);
                    parse_pairs(chars, &mut entry)?;
                    arr.push(Ir::Table(entry));
                }
                _ => return Err(Error),
            }
        }
    }

    Ok(())
}
