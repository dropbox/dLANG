use std::{env, path::Path};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=TSWIFT_Z3_LIB_DIR");
    println!("cargo:rerun-if-env-changed=Z3_LIB_DIR");
    println!("cargo:rerun-if-env-changed=Z3_SYS_Z3_LIB_DIR");

    if env::var_os("CARGO_FEATURE_Z3_FALLBACK").is_none() {
        return;
    }

    if let Some(lib_dir) = env::var("TSWIFT_Z3_LIB_DIR")
        .ok()
        .or_else(|| env::var("Z3_SYS_Z3_LIB_DIR").ok())
        .or_else(|| env::var("Z3_LIB_DIR").ok())
    {
        if Path::new(&lib_dir).exists() {
            println!("cargo:rustc-link-search=native={lib_dir}");
        }
        return;
    }

    if cfg!(target_os = "macos") {
        for dir in ["/opt/homebrew/lib", "/usr/local/lib"] {
            let dir_path = Path::new(dir);
            if dir_path.join("libz3.dylib").exists() || dir_path.join("libz3.a").exists() {
                println!("cargo:rustc-link-search=native={dir}");
                break;
            }
        }
    }
}
