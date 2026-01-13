//! tC CLI: tc-verify
//!
//! Command-line interface for C verification.

use clap::{Parser, Subcommand};
use std::path::PathBuf;
use tc_verify::{verify_file, Backend, VerifyOptions};

#[derive(Parser)]
#[command(name = "tc-verify")]
#[command(author = "Andrew Yates <ayates@dropbox.com>")]
#[command(version = "0.1.0")]
#[command(about = "Verify C code with ACSL specs and translation validation")]
#[command(long_about = "
tC: Trusted C Verification

Verify the source, validate the compilation, keep the performance.

tC verifies C code against ACSL specifications, optionally validates
that Clang compilation preserves semantics, and checks FFI boundaries
with Rust and Swift code.
")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify a C file against its ACSL specifications
    Verify {
        /// C file to verify
        file: PathBuf,

        /// Enable translation validation (requires Alive2)
        #[arg(long)]
        translate_validate: bool,

        /// Rust file for FFI boundary checking
        #[arg(long)]
        rust_bridge: Option<PathBuf>,

        /// Swift file for FFI boundary checking
        #[arg(long)]
        swift_bridge: Option<PathBuf>,

        /// Verification backend (z4, kani, lean5)
        #[arg(long, default_value = "z4")]
        backend: String,

        /// Verbose output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Check FFI boundary between C and Rust/Swift
    FfiCheck {
        /// C file
        #[arg(long, short = 'c')]
        c_file: PathBuf,

        /// Rust file
        #[arg(long)]
        rust: Option<PathBuf>,

        /// Swift file
        #[arg(long)]
        swift: Option<PathBuf>,

        /// Verbose output
        #[arg(short, long)]
        verbose: bool,
    },

    /// Parse and display ACSL specs from a C file
    ParseSpecs {
        /// C file to parse
        file: PathBuf,
    },
}

fn main() -> anyhow::Result<()> {
    // Initialize logging
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive(tracing::Level::INFO.into()),
        )
        .init();

    let cli = Cli::parse();

    match cli.command {
        Commands::Verify {
            file,
            translate_validate,
            rust_bridge,
            swift_bridge,
            backend,
            verbose,
        } => {
            let backend = match backend.as_str() {
                "z4" => Backend::Z4,
                "kani" => Backend::Kani,
                "lean5" => Backend::Lean5,
                _ => {
                    eprintln!("Unknown backend: {}. Using z4.", backend);
                    Backend::Z4
                }
            };

            let options = VerifyOptions {
                translation_validation: translate_validate,
                rust_bridge,
                swift_bridge,
                backend,
                verbose,
            };

            println!("Verifying {}...", file.display());
            let result = verify_file(&file, &options)?;

            if result.is_verified() {
                println!("Result: VERIFIED ({}/{} VCs proven)", result.proven_count, result.vc_count);
            } else {
                println!("Result: FAILED ({}/{} VCs proven)", result.proven_count, result.vc_count);
                for cex in &result.counterexamples {
                    println!("  Counterexample in {}: {}", cex.function, cex.condition);
                }
            }

            for warning in &result.warnings {
                println!("Warning: {}", warning);
            }

            if result.is_verified() {
                Ok(())
            } else {
                std::process::exit(1);
            }
        }

        Commands::FfiCheck {
            c_file,
            rust,
            swift,
            verbose: _,
        } => {
            println!("FFI boundary check:");
            println!("  C file: {}", c_file.display());
            if let Some(r) = rust {
                println!("  Rust file: {}", r.display());
            }
            if let Some(s) = swift {
                println!("  Swift file: {}", s.display());
            }
            println!("FFI checking not yet implemented.");
            Ok(())
        }

        Commands::ParseSpecs { file } => {
            println!("Parsing ACSL specs from {}...", file.display());
            let specs = tc_verify::parser::extract_specs(&file)?;
            println!("Found {} function specs", specs.len());
            for spec in specs {
                println!("  {}: {} requires, {} ensures",
                    spec.name,
                    spec.requires.len(),
                    spec.ensures.len()
                );
            }
            Ok(())
        }
    }
}
