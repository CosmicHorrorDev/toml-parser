// A build script to generate a test per provided test vector

use std::{
    env, fs,
    path::{Path, PathBuf},
};

fn main() {
    env::set_current_dir(&project_root()).unwrap();

    let out_dir_env = env::var_os("OUT_DIR").unwrap();
    let out_dir = Path::new(&out_dir_env);
    let submodule_canary_path = out_dir.join("submodule_canary.rs");
    let valid_vectors_path = out_dir.join("test_valid.rs");
    let invalid_vectors_path = out_dir.join("test_invalid.rs");

    // Build and name our list of test vectors
    let test_vec_dir = Path::new("toml-test/tests/assets/toml-test/tests");

    let submodule_canary = if test_vec_dir.is_dir() {
        "#[test] fn submodules_are_initialized() {}"
    } else {
        "#[test] fn you_must_init_submodules() { panic!(\"The test suite requires submodules to be \
        initialized. Run `git submodule update --init --recursive`\") }"
    };
    fs::write(&submodule_canary_path, submodule_canary).unwrap();

    let test_vector_list = fs::read_to_string(&test_vec_dir.join("files-toml-1.0.0")).unwrap();

    let mut invalid_vectors = String::new();
    let mut valid_vectors = String::new();

    let mut test_vector_it = test_vector_list
        .lines()
        .filter(|line| !line.trim().is_empty());

    loop {
        let Some(test_vector) = test_vector_it.next() else {
            break;
        };

        if test_vector.starts_with("invalid") {
            invalid_vectors += &format!(
                "#[test]\nfn {}() {{\n    check_invalid(\"{}\");\n}}\n\n",
                sanitize_test_vector_name(test_vector),
                test_vector,
            );
        } else if test_vector.starts_with("valid") {
            let rel_toml_path = test_vector_it.next().unwrap();
            valid_vectors += &format!(
                "#[test]\nfn {}() {{\n    check_valid(\"{}\", \"{}\");\n}}\n\n",
                sanitize_test_vector_name(test_vector),
                test_vector,
                rel_toml_path,
            );
        } else {
            panic!("Unexpected test vector line: {}", test_vector);
        }
    }

    fs::write(&invalid_vectors_path, &invalid_vectors).unwrap();
    fs::write(&valid_vectors_path, &valid_vectors).unwrap();
}

fn project_root() -> PathBuf {
    Path::new(&env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(1)
        .unwrap()
        .to_path_buf()
}

fn sanitize_test_vector_name(rel_path: &str) -> String {
    rel_path
        .trim_end_matches(".json")
        .trim_end_matches(".toml")
        .replace(['-', '/'], "_")
}
