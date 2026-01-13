# VS Code Extension

tRust provides a VS Code extension for IDE integration with inline verification feedback.

## Installation

The extension is in `editors/vscode/`:

```bash
cd editors/vscode
npm install
npm run compile
```

Then in VS Code:
1. Open Command Palette (`Ctrl+Shift+P` / `Cmd+Shift+P`)
2. Run "Extensions: Install from VSIX..."
3. Select the generated `.vsix` file

## Features

### Inline Verification Status

After verification, functions show their status:
- ✓ Green checkmark: PROVEN
- ✗ Red X: DISPROVEN
- ? Yellow question mark: UNKNOWN

Status appears both in the gutter and as end-of-line decorations.

### CodeLens

Above each function with specifications, CodeLens shows verification status:

```rust,ignore
// ✓ PROVEN
#[ensures("result >= 0")]
fn abs(x: i32) -> i32 { ... }

// ✗ DISPROVEN
#[ensures("result > 0")]
fn buggy(x: i32) -> i32 { ... }
```

### Counterexample on Hover

When verification fails, hover over the function to see the counterexample:

```console
Verification DISPROVEN
Counterexample: x = -2147483648
```

### Quick Fix Suggestions

The extension suggests fixes for common verification errors:

```rust,ignore
// Error: potential overflow
fn abs(x: i32) -> i32 {
    -x  // Quick fix: "Add precondition #[requires("x > i32::MIN")]"
}
```

### Diagnostics

Verification errors appear in the Problems panel with error codes:

```console
E0902: Postcondition could not be proven
  ensures(result >= 0)
  at line 5, column 1
```

## Commands

Access via Command Palette (`Ctrl+Shift+P` / `Cmd+Shift+P`):

| Command | Shortcut | Description |
|---------|----------|-------------|
| `trust.verifyFile` | `Ctrl+Shift+T V` | Verify current file |
| `trust.verifyWorkspace` | `Ctrl+Shift+T W` | Verify all .rs files |
| `trust.clearCache` | | Clear verification cache |
| `trust.showCacheStats` | | Show cache statistics |

### Keyboard Shortcuts

- `Ctrl+Shift+T V` (Mac: `Cmd+Shift+T V`): Verify current file
- `Ctrl+Shift+T W` (Mac: `Cmd+Shift+T W`): Verify workspace
- `Ctrl+Shift+T C` (Mac: `Cmd+Shift+T C`): Clear cache

## Configuration

Settings in VS Code (File > Preferences > Settings):

| Setting | Default | Description |
|---------|---------|-------------|
| `trust.trustcPath` | Auto-detect | Path to trustc binary |
| `trust.verifyOnSave` | `false` | Verify file when saved |
| `trust.outputFormat` | `json` | Output format (json/text) |
| `trust.useGlobalCache` | `false` | Use global verification cache |

### Example settings.json

```json
{
  "trust.trustcPath": "/path/to/tRust/bin/trustc",
  "trust.verifyOnSave": true,
  "trust.useGlobalCache": true
}
```

## Status Bar

The status bar shows verification summary:

```console
tRust: 5/5 ✓ | 0 ✗ | 0 ?
```

Click to open the output panel with detailed results.

## Output Panel

View detailed verification output in the "tRust" output channel:

1. View > Output (or `Ctrl+Shift+U`)
2. Select "tRust" from the dropdown

## Explain Error

When an error code appears (E09xx), right-click for "Explain Error" to see detailed documentation:

```text
E0902: Postcondition could not be proven

A postcondition specified with #[ensures("...")] could not be verified.

This means the SMT solver could not prove that the postcondition
holds for all valid inputs...
```

## Troubleshooting

### "trustc not found"

Set `trust.trustcPath` to the full path of your trustc binary:

```json
{
  "trust.trustcPath": "/Users/me/tRust/bin/trustc"
}
```

### Verification not running

Check the Output panel for errors. Common issues:
- Missing sysroot: Set `TRUST_SYSROOT` environment variable
- Compilation errors: Fix Rust errors before verification

### Slow verification

- Enable caching: Set `trust.useGlobalCache` to `true`
- Verify on demand instead of on-save

## Development

To modify the extension:

```bash
cd editors/vscode
npm install
npm run watch  # Compile in watch mode
```

Press F5 in VS Code to launch the Extension Development Host.

## Next Steps

- [Cargo Integration](./cargo.md) - Use tRust with Cargo
- [JSON Output](./json.md) - Programmatic access to verification results
