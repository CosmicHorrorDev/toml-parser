// Use a build script to generate out test suite with test vectors provided by:
// https://github.com/toml-lang/toml-test

include!(concat!(env!("OUT_DIR"), "/submodule_canary.rs"));
include!(concat!(env!("OUT_DIR"), "/test_invalid.rs"));
include!(concat!(env!("OUT_DIR"), "/test_valid.rs"));

// And here is all the helper code that doesn't need to live in the build script

use std::{collections::BTreeMap, fs, path::Path};

use just_a_toml_parser::{
    parse, Datetime as TomlDatetime, Def as TomlDef, Kind as TomlKind, Table as TomlTable,
    Value as TomlValue,
};
use serde_json::{Map as JsonMap, Value as JsonValue};

#[track_caller]
fn check_invalid(rel_path: &str) {
    let test_vector_path = Path::new("tests/assets/toml-test/tests").join(rel_path);
    let test_vector_bytes = fs::read(&test_vector_path).unwrap();
    // > A TOML file must be a valid UTF-8 encoded Unicode document.
    if let Ok(test_vector) = String::from_utf8(test_vector_bytes) {
        parse(&test_vector).unwrap_err();
    }
}

#[track_caller]
fn check_valid(rel_json_path: &str, rel_toml_path: &str) {
    let json_path = Path::new("tests/assets/toml-test/tests").join(rel_json_path);
    let toml_path = Path::new("tests/assets/toml-test/tests").join(rel_toml_path);
    let json_vector = fs::read_to_string(&json_path).unwrap();
    let toml_vector = fs::read_to_string(&toml_path).unwrap();

    let toml_value = parse(&toml_vector).unwrap();
    let json_value = serde_json::from_str(&json_vector).unwrap();
    let ideal = tagged_json_to_toml_value(json_value);

    assert_eq!(
        TestValue::from(TomlValue::Table(toml_value)),
        TestValue::from(ideal),
    );
}

fn tagged_json_to_toml_value(json: JsonValue) -> TomlValue {
    match json {
        JsonValue::Object(obj) => match (obj.get("type"), obj.get("value")) {
            (Some(ty), Some(val)) => {
                let ty_str = ty.as_str().unwrap();
                let val_str = val.as_str().unwrap();
                match ty_str {
                    "bool" => match val_str {
                        "true" => TomlValue::Boolean(true),
                        "false" => TomlValue::Boolean(false),
                        _ => unreachable!(),
                    },
                    "integer" => {
                        let val_int: i64 = val_str.parse().unwrap();
                        TomlValue::Integer(val_int)
                    }
                    "string" => TomlValue::String(val_str.to_owned()),
                    "float" => {
                        let val_float: f64 = val_str.parse().unwrap();
                        TomlValue::Float(val_float)
                    }
                    "date-local" => {
                        let dt: TomlDatetime = val_str.parse().unwrap();
                        assert!(dt.date.is_some() && dt.time.is_none() && dt.offset.is_none());
                        TomlValue::Datetime(dt)
                    }
                    "datetime" => {
                        let dt: TomlDatetime = val_str.parse().unwrap();
                        assert!(dt.date.is_some() && dt.time.is_some() && dt.offset.is_some());
                        TomlValue::Datetime(dt)
                    }
                    "datetime-local" => {
                        let dt: TomlDatetime = val_str.parse().unwrap();
                        assert!(dt.date.is_some() && dt.time.is_some() && dt.offset.is_none());
                        TomlValue::Datetime(dt)
                    }
                    "time-local" => {
                        let dt: TomlDatetime = val_str.parse().unwrap();
                        assert!(dt.date.is_none() && dt.time.is_some() && dt.offset.is_none());
                        TomlValue::Datetime(dt)
                    }
                    _ => todo!(),
                }
            }
            _ => {
                let table: BTreeMap<_, _> = obj
                    .into_iter()
                    .map(|(k, v)| (k, tagged_json_to_toml_value(v)))
                    .collect();
                TomlValue::Table(table)
            }
        },
        JsonValue::Array(arr) => {
            let arr = arr.into_iter().map(tagged_json_to_toml_value).collect();
            TomlValue::Array(arr)
        }
        _ => todo!(),
    }
}

#[derive(Debug, PartialEq)]
enum TestValue {
    Boolean(bool),
    Integer(i64),
    Float(NanEqualFloat),
    String(String),
    Array(Vec<TestValue>),
    Table(BTreeMap<String, TestValue>),
    Datetime(TomlDatetime),
}

impl From<TomlValue> for TestValue {
    fn from(toml: TomlValue) -> Self {
        match toml {
            TomlValue::Boolean(b) => Self::Boolean(b),
            TomlValue::Integer(i) => Self::Integer(i),
            TomlValue::Float(f) => Self::Float(NanEqualFloat(f)),
            TomlValue::String(s) => Self::String(s),
            TomlValue::Array(a) => Self::Array(a.into_iter().map(Self::from).collect()),
            TomlValue::Table(t) => {
                Self::Table(t.into_iter().map(|(k, v)| (k, Self::from(v))).collect())
            }
            TomlValue::Datetime(d) => Self::Datetime(d),
        }
    }
}

/// Normally NaN != NaN, but we want to have them be equal for checking validity
#[derive(Debug)]
struct NanEqualFloat(f64);

impl PartialEq for NanEqualFloat {
    fn eq(&self, other: &Self) -> bool {
        if self.0.is_nan() && other.0.is_nan() {
            self.0.is_sign_negative() == self.0.is_sign_negative()
        } else {
            self.0 == other.0
        }
    }
}
