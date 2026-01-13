# tRust Spec Repository

This directory contains specifications for external crates that are not part of the Rust standard library.

## Structure

```
specs/
├── README.md           # This file
├── spec_format.md      # TOML format documentation
├── community/          # Community-contributed specs (reviewed)
│   ├── regex.toml
│   ├── serde.toml
│   └── ...
└── local/              # Local specs (not committed)
```

## Contributing Specs

1. Create a TOML file following the format in `spec_format.md`
2. Add tests that use the specs to verify they're correct
3. Submit a PR to add to `community/`

## Spec File Format

Spec files use TOML format with the following structure:

```toml
[crate]
name = "regex"
version = "1.10"  # Minimum version these specs apply to
trust_level = "audited"  # verified | audited | assumed

[[function]]
name = "regex::Regex::new"
preconditions = []
postconditions = ["result.is_ok() || result.is_err()"]
effects = ["Alloc"]

[[function]]
name = "regex::Regex::is_match"
preconditions = []
postconditions = []
pure = true
```

See `spec_format.md` for complete documentation.
