use std::path::Path;

#[test]
fn sil_fixtures_use_expected_suffixes() {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let sil_examples_dir = Path::new(manifest_dir).join("tests/sil_examples");

    let mut invalid = Vec::new();
    for entry in std::fs::read_dir(&sil_examples_dir).expect("failed to read tests/sil_examples") {
        let entry = entry.expect("failed to read dir entry");
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "sil") {
            let filename = entry.file_name();
            let filename = filename.to_string_lossy();
            let ok = filename.ends_with("_safe.sil")
                || filename.ends_with("_unsafe.sil")
                || filename.ends_with("_should_fail.sil")
                || filename.ends_with("_unknown.sil");
            if !ok {
                invalid.push(filename.to_string());
            }
        }
    }

    invalid.sort();
    assert!(
        invalid.is_empty(),
        "SIL fixtures must end with `_safe.sil`, `_unsafe.sil`, `_should_fail.sil`, or `_unknown.sil`.\nInvalid:\n{}",
        invalid.join("\n")
    );
}
