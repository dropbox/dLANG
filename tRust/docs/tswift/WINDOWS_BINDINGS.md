# Verified Windows Bindings

**Native Windows apps in pure Rust with verified WinUI 3 bindings**

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Windows App (dterm, Dash)                 │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│   ┌─────────────────────────────────────────────────────┐   │
│   │              Your Rust UI Code                       │   │
│   │                                                      │   │
│   │   fn create_terminal_window() {                      │   │
│   │       let window = Window::new(title, size)?;        │   │
│   │       let nav = NavigationView::new()?;              │   │
│   │       // ...                                         │   │
│   │   }                                                  │   │
│   │                                                      │   │
│   │   Verified by: tRust                                 │   │
│   └─────────────────────────┬───────────────────────────┘   │
│                             │                                │
│   ┌─────────────────────────▼───────────────────────────┐   │
│   │         Verified Windows Bindings                    │   │
│   │                                                      │   │
│   │   #[requires(title.len() <= MAX_TITLE)]              │   │
│   │   #[ensures(result.is_ok() => result.is_valid())]    │   │
│   │   fn CreateWindowExW(...) -> Result<HWND>;           │   │
│   │                                                      │   │
│   │   ~50-100 functions with full specs                  │   │
│   │   Verified by: tRust                                 │   │
│   └─────────────────────────┬───────────────────────────┘   │
│                             │                                │
│   ┌─────────────────────────▼───────────────────────────┐   │
│   │              Windows APIs (WinUI 3, Win32)           │   │
│   │                                                      │   │
│   │   Trust level: #[trusted] (Microsoft's code)         │   │
│   └─────────────────────────────────────────────────────┘   │
│                                                              │
├─────────────────────────────────────────────────────────────┤
│                        Rust Core                             │
│                                                              │
│   Parser │ Grid │ Voice │ LLM Client                        │
│                                                              │
│   Verified by: tRust (same as everything else)              │
└─────────────────────────────────────────────────────────────┘
```

---

## Why Custom Bindings

| Approach | Effort | Verification |
|----------|--------|--------------|
| tCpp (verified C++ compiler) | Massive | Proves everything, including memory safety |
| windows-rs (as-is) | Zero | No specs, trust it |
| **Custom verified bindings** | **Small** | **Full specs on your API surface** |

Rust already guarantees memory safety. Custom bindings just add functional specs to the Windows calls you actually use.

---

## Binding Categories

### 1. Window Management (~15 functions)

```rust
// src/windows_bindings/window.rs

use crate::specs::*;

#[repr(transparent)]
pub struct HWND(pub(crate) isize);

impl HWND {
    #[ensures(result == self.0 != 0)]
    pub fn is_valid(&self) -> bool {
        self.0 != 0
    }
}

#[requires(width > 0 && height > 0)]
#[requires(title.len() <= 256)]
#[ensures(result.is_ok() => result.unwrap().is_valid())]
pub fn create_window(
    title: &str,
    width: u32,
    height: u32,
    style: WindowStyle,
) -> Result<HWND, WindowsError> {
    unsafe {
        // Raw FFI call
        let hwnd = CreateWindowExW(
            0,
            class_name.as_ptr(),
            title.to_wide().as_ptr(),
            style.bits(),
            CW_USEDEFAULT, CW_USEDEFAULT,
            width as i32, height as i32,
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            get_module_handle(),
            std::ptr::null_mut(),
        );

        if hwnd.is_null() {
            Err(WindowsError::last())
        } else {
            Ok(HWND(hwnd as isize))
        }
    }
}

#[requires(hwnd.is_valid())]
pub fn show_window(hwnd: HWND, cmd: ShowCommand) {
    unsafe {
        ShowWindow(hwnd.0 as *mut _, cmd as i32);
    }
}

#[requires(hwnd.is_valid())]
#[ensures(result.width >= 0 && result.height >= 0)]
pub fn get_client_rect(hwnd: HWND) -> Rect {
    unsafe {
        let mut rect = std::mem::zeroed();
        GetClientRect(hwnd.0 as *mut _, &mut rect);
        Rect::from_win32(rect)
    }
}
```

### 2. WinUI 3 Controls (~20 functions)

```rust
// src/windows_bindings/winui.rs

/// WinUI 3 NavigationView
pub struct NavigationView {
    inner: INavigationView,
}

impl NavigationView {
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn new() -> Result<Self, WindowsError> {
        // WinRT activation
    }

    #[requires(self.is_valid())]
    #[requires(!title.is_empty())]
    pub fn add_item(&mut self, title: &str, icon: Icon) -> Result<(), WindowsError> {
        // Add navigation item
    }

    #[requires(self.is_valid())]
    #[ensures(result.is_some() => result.unwrap() < self.item_count())]
    pub fn selected_index(&self) -> Option<usize> {
        // Get selected item
    }
}

/// WinUI 3 Grid layout
pub struct Grid {
    inner: IGrid,
}

impl Grid {
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn new() -> Result<Self, WindowsError>;

    #[requires(self.is_valid())]
    #[requires(row >= 0 && col >= 0)]
    pub fn add_child(&mut self, child: &impl UIElement, row: u32, col: u32);
}

/// WinUI 3 TextBlock
pub struct TextBlock {
    inner: ITextBlock,
}

impl TextBlock {
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn new(text: &str) -> Result<Self, WindowsError>;

    #[requires(self.is_valid())]
    pub fn set_text(&mut self, text: &str);
}
```

### 3. Direct2D / DirectWrite (~15 functions)

```rust
// src/windows_bindings/graphics.rs

/// Direct2D render target
pub struct RenderTarget {
    inner: ID2D1RenderTarget,
}

impl RenderTarget {
    #[requires(hwnd.is_valid())]
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn for_hwnd(hwnd: HWND) -> Result<Self, WindowsError>;

    #[requires(self.is_valid())]
    pub fn begin_draw(&mut self);

    #[requires(self.is_valid())]
    #[ensures(result.is_ok())]  // Draw completed successfully
    pub fn end_draw(&mut self) -> Result<(), WindowsError>;

    #[requires(self.is_valid())]
    #[requires(rect.is_valid())]
    pub fn fill_rect(&mut self, rect: Rect, brush: &Brush);
}

/// DirectWrite text layout
pub struct TextLayout {
    inner: IDWriteTextLayout,
}

impl TextLayout {
    #[requires(!text.is_empty())]
    #[requires(max_width > 0.0 && max_height > 0.0)]
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn new(
        text: &str,
        format: &TextFormat,
        max_width: f32,
        max_height: f32,
    ) -> Result<Self, WindowsError>;

    #[requires(self.is_valid())]
    #[ensures(result.width >= 0.0 && result.height >= 0.0)]
    pub fn metrics(&self) -> TextMetrics;
}
```

### 4. System Integration (~10 functions)

```rust
// src/windows_bindings/system.rs

/// System tray icon
pub struct TrayIcon {
    hwnd: HWND,
    id: u32,
}

impl TrayIcon {
    #[requires(hwnd.is_valid())]
    #[ensures(result.is_ok() => result.unwrap().is_valid())]
    pub fn new(hwnd: HWND, icon: Icon, tooltip: &str) -> Result<Self, WindowsError>;

    #[requires(self.is_valid())]
    pub fn show_notification(&self, title: &str, message: &str);
}

/// Toast notification
#[requires(!title.is_empty())]
pub fn show_toast(title: &str, body: &str) -> Result<(), WindowsError>;

/// Dark mode detection
#[ensures(result == true || result == false)]  // Always returns valid bool
pub fn is_dark_mode() -> bool;

/// DPI awareness
#[ensures(result >= 96)]  // Minimum DPI
pub fn get_dpi() -> u32;
```

---

## Crate Structure

```
windows-verified/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Re-exports
│   ├── error.rs            # WindowsError type
│   ├── types.rs            # HWND, Rect, etc.
│   ├── window.rs           # Window management
│   ├── winui.rs            # WinUI 3 controls
│   ├── graphics.rs         # Direct2D/DirectWrite
│   ├── system.rs           # Tray, notifications, etc.
│   └── ffi/
│       ├── mod.rs
│       ├── win32.rs        # Raw Win32 FFI
│       ├── winrt.rs        # Raw WinRT FFI
│       └── d2d.rs          # Raw Direct2D FFI
└── tests/
    ├── window_tests.rs
    ├── winui_tests.rs
    └── graphics_tests.rs
```

---

## Example: dterm Window

```rust
use windows_verified::*;

#[requires(config.is_valid())]
#[ensures(result.is_ok() => result.unwrap().is_valid())]
pub fn create_dterm_window(config: &TerminalConfig) -> Result<TerminalWindow, Error> {
    // Create main window
    let hwnd = create_window(
        &config.title,
        config.width,
        config.height,
        WindowStyle::OVERLAPPED_WINDOW,
    )?;

    // Create WinUI navigation (tabs)
    let nav = NavigationView::new()?;
    nav.add_item("Terminal 1", Icon::Terminal)?;
    nav.add_item("Settings", Icon::Settings)?;

    // Create render target for terminal
    let render_target = RenderTarget::for_hwnd(hwnd)?;

    // Create text layout engine
    let text_format = TextFormat::new("Cascadia Code", 14.0)?;

    Ok(TerminalWindow {
        hwnd,
        nav,
        render_target,
        text_format,
    })
}
```

All verified by tRust. No C++. No tCpp.

---

## Trust Boundary

```
┌─────────────────────────────────────────────────┐
│  YOUR CODE (verified by tRust)                  │
│                                                 │
│  Rust UI + Rust Core + Verified Bindings        │
└─────────────────────┬───────────────────────────┘
                      │
                      │ #[trusted] boundary
                      │
┌─────────────────────▼───────────────────────────┐
│  MICROSOFT'S CODE (trusted, not verified)       │
│                                                 │
│  WinUI 3, Win32, DirectX, Windows Runtime       │
│                                                 │
│  Assumption: Microsoft's APIs work as documented│
└─────────────────────────────────────────────────┘
```

---

## Comparison to Other Platforms

| Platform | Your Code | Native APIs | Verification |
|----------|-----------|-------------|--------------|
| iOS | Swift (thin) | UIKit/SwiftUI | tSwift |
| macOS | Swift (thin) | AppKit/SwiftUI | tSwift |
| Android | Kotlin (thin) | Android SDK | tKotlin |
| **Windows** | **Rust (thin)** | **WinUI 3/Win32** | **tRust** |
| Linux | Rust | GTK4/X11 | tRust |

Windows is the only platform where the UI layer is also Rust. Simplest verification story.

---

## Implementation Plan

### Phase 1: Core Window (~2 days)
- [ ] HWND wrapper with specs
- [ ] create_window, show_window, destroy_window
- [ ] Message loop
- [ ] Basic event handling

### Phase 2: WinUI 3 Controls (~3 days)
- [ ] NavigationView
- [ ] Grid, StackPanel
- [ ] TextBlock, TextBox
- [ ] Button, ToggleSwitch
- [ ] Basic styling

### Phase 3: Graphics (~2 days)
- [ ] Direct2D render target
- [ ] DirectWrite text layout
- [ ] Basic drawing primitives

### Phase 4: System Integration (~1 day)
- [ ] Tray icon
- [ ] Notifications
- [ ] Dark mode
- [ ] DPI handling

### Total: ~8 days

Compare to tCpp: ~months

---

## Summary

**No tCpp. Just Rust.**

```
┌─────────────────────────────────────────┐
│         Verification Tools               │
├─────────────────────────────────────────┤
│  tRust   - Rust (core + Windows + Linux)│
│  tSwift  - Swift (iOS/macOS UI)         │
│  tKotlin - Kotlin (Android UI)          │
│                                         │
│  That's it. Three tools.                │
└─────────────────────────────────────────┘
```
