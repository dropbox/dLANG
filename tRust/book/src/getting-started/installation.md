# Installation

This guide covers installing tRust on your system.

## Prerequisites

tRust requires:
- **Rust 1.75+**: Install via [rustup](https://rustup.rs/)
- **CMake and Ninja**: For building the Z4 SMT solver
- **Git**: For cloning the repository

### macOS

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install build dependencies
brew install cmake ninja
```

### Linux (Ubuntu/Debian)

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Install build dependencies
sudo apt install cmake ninja-build
```

## Building tRust

Clone the repository and build the stage 1 compiler:

```bash
git clone https://github.com/dropbox/dLANG/tRust.git
cd tRust

# Build the compiler (takes ~10-15 minutes first time)
./rebuild.sh
```

The build script will:
1. Clone/update the `kani_fast` verification library
2. Build the stage 1 rustc compiler with verification support
3. Set up the `trustc` and `cargo-trust` wrappers

## Verifying Installation

After building, verify the installation:

```bash
# Check trustc is available
./bin/trustc --version

# Run a simple verification
echo '#[ensures("result >= 0")]
fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }' > /tmp/test.rs

./bin/trustc /tmp/test.rs
```

You should see output showing the verification result.

## Shell Completion

tRust provides shell completion scripts for `trustc`, `trustv`, and `cargo-trust` in `bin/completions/`:

```bash
# Bash (add to ~/.bashrc)
source /path/to/tRust/bin/completions/trustc.bash
source /path/to/tRust/bin/completions/trustv.bash
source /path/to/tRust/bin/completions/cargo-trust.bash

# Zsh (add tRust completions to fpath before compinit in ~/.zshrc)
fpath=(/path/to/tRust/bin/completions $fpath)
autoload -Uz compinit && compinit
# Or copy the _trustc, _trustv, _cargo-trust files to a directory already in fpath

# Fish (symlink or copy to ~/.config/fish/completions/)
ln -s /path/to/tRust/bin/completions/trustc.fish ~/.config/fish/completions/
ln -s /path/to/tRust/bin/completions/trustv.fish ~/.config/fish/completions/
ln -s /path/to/tRust/bin/completions/cargo-trust.fish ~/.config/fish/completions/
```

## Environment Variables

tRust recognizes these environment variables:

| Variable | Description |
|----------|-------------|
| `TRUST_SYSROOT` | Override the sysroot path |
| `TRUST_CACHE_DIR` | Project cache directory (default: `.trust_cache`) |
| `TRUST_GLOBAL_CACHE_DIR` | Global cache location (default: `~/.cache/trust/`) |
| `TRUST_USE_GLOBAL_CACHE` | Enable global caching (`1` to enable) |
| `TRUST_JSON_OUTPUT` | Enable JSON output mode (`1` to enable) |

## VS Code Extension

For IDE integration, install the VS Code extension:

```bash
cd editors/vscode
npm install
npm run compile
```

Then in VS Code, use "Install from VSIX..." to install the extension.

See [VS Code Extension](../tooling/vscode.md) for details.

## Next Steps

Now that tRust is installed, continue to [Your First Verified Program](./first-program.md) to write and verify your first function.
