# tRust Verification Extension for VS Code

This extension provides integrated formal verification support for Rust code using the tRust compiler.

## Features

- **CodeLens Verification Status**: See verification status above each function definition (✓ PROVEN, ✗ DISPROVEN, ? UNKNOWN, ○ no specs). Click to view details.
- **Inline Verification Status**: See which functions are verified, disproven, or unknown directly in the editor (gutter + inline icon)
- **Diagnostics**: Verification errors and warnings appear in the Problems panel
- **Counterexample Display**: When verification fails, see the counterexample values that cause the failure
- **Quick Fixes**: Verification diagnostics include quick fixes to copy suggestions, insert suggestion comments, or show error explanations
- **On-Save Verification**: Automatically verify files when you save them
- **Cache Integration**: Uses tRust's verification cache for fast incremental verification
- **Workspace Verification**: Verify all Rust files in the workspace with progress tracking

## Requirements

- tRust compiler (`trustc`) must be installed and accessible
- Configure `trust.trustcPath` in settings if `trustc` is not in your PATH

## Extension Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `trust.trustcPath` | `""` | Path to the trustc binary (empty = auto-detect) |
| `trust.verifyOnSave` | `true` | Automatically verify files on save |
| `trust.verifyOnOpen` | `false` | Automatically verify files when opened |
| `trust.showInlineStatus` | `true` | Show inline verification status decorations |
| `trust.useGlobalCache` | `false` | Use global verification cache shared across projects |
| `trust.verboseOutput` | `false` | Enable verbose verification output |
| `trust.showCodeLens` | `true` | Show CodeLens with verification status above function definitions |

## Commands

| Command | Keyboard Shortcut | Description |
|---------|-------------------|-------------|
| **tRust: Verify Current File** | `Ctrl+Alt+T` (`Cmd+Alt+T` on Mac) | Verify the current Rust file |
| **tRust: Verify Workspace** | `Ctrl+Alt+Shift+T` (`Cmd+Alt+Shift+T` on Mac) | Verify all Rust files in the workspace |
| **tRust: Explain Error Code** | - | Show detailed explanation for a verification error code (E09xx) |
| **tRust: Clear Verification Cache** | - | Clear the verification cache |
| **tRust: Show Cache Statistics** | - | Display cache statistics in the output channel

## Status Bar

The status bar shows a summary of verification results:
- ✓ Green: All functions verified
- ⚠ Yellow: Some functions have unknown status
- ✗ Red: Some functions have verification failures

Click the status bar item to re-run verification.

## Building

```bash
cd editors/vscode
npm install
npm run compile
```

## Installing Locally

1. Build the extension: `npm run compile`
2. Package it: `npx vsce package`
3. Install the `.vsix` file in VS Code

## JSON Output Format

This extension uses tRust's JSON output mode (`--output-format=json`). The JSON schema includes:

- `summary`: Overall counts (verified, disproven, unknown, errors)
- `functions`: Per-function verification results with status and counterexamples
- `overflow_errors`: Potential arithmetic overflow errors
- `bounds_errors`: Potential array index out of bounds errors
- `effect_errors`: Effect system violations
- `wiring`: Wiring verification results

See `upstream/rustc/compiler/rustc_verify/src/json_output.rs` for the full schema.

## Contributing

This extension is part of the tRust project. See the main repository for contribution guidelines.

## License

MIT OR Apache-2.0 (same as Rust)
