# Wiring Verification: Proving Applications Are Properly Connected

## The Problem

**AI writes code that compiles but doesn't work.**

A common failure mode when AI generates applications:

```
AI: "Done! Your app is complete."
User: *runs app*
User: *nothing happens*
```

The code compiles. Types check. No runtime errors. But the button doesn't trigger the action. The form doesn't submit. The route doesn't connect to the handler.

**The application isn't wired together.**

---

## What Is "Wiring"?

Wiring is the connective tissue of an application:

```
User clicks button
    → Event handler fires
        → API call made
            → Database updated
                → UI refreshes
```

Each arrow is a wire. If any wire is missing, the application is broken.

Traditional verification proves *what* code does. Wiring verification proves *that code is connected*.

---

## Why Wiring Fails

### Fragmented Context

AI writes each component in isolation:

```rust
// AI writes this in one context window
fn handle_checkout() {
    // Implementation
}

// AI writes this in another context window
fn PaymentButton() {
    // Never calls handle_checkout
    // AI forgot the connection
}
```

Each piece is correct. The composition is wrong.

### Silent Failures

Unwired code doesn't crash - it silently does nothing:

```rust
async fn save_user(user: User) -> Result<()> {
    // AI generated this
    Ok(())  // Forgot to actually call database
}
```

Tests pass (function returns Ok). App is broken.

### Implicit Connections

Many frameworks rely on convention:

```rust
// Axum route
Router::new().route("/api/user", post(create_user))

// Handler exists but with wrong signature
async fn create_user(user: User) { }  // Missing extractors
```

Compiles fine. Fails at runtime.

---

## tRust Wiring Verification

### Tier 1: Reachability Proofs

The AI annotates **hot spots** - states that users must be able to reach:

```rust
#[wire_start]
fn main() {
    App::run()
}

#[wire_state("checkout")]
#[wire_must_reach("payment_success, payment_error")]
fn begin_checkout(cart: Cart) {
    // User starts checkout flow
}

#[wire_state("payment_success")]
fn payment_confirmed(receipt: Receipt) {
    // Must be reachable from checkout
}

#[wire_state("payment_error")]
#[wire_recoverable]  // User can recover from this state
fn payment_failed(error: PaymentError) {
    // Must be reachable from checkout
}
```

**tRust proves:**
1. Every `#[wire_state]` is reachable from `#[wire_start]`
2. Every `#[wire_must_reach]` target is reachable from that state
3. Every `#[wire_recoverable]` state has a path to a non-error state

### Tier 2: Path Analysis

tRust doesn't just prove reachability - it analyzes the paths:

**Anomaly Detection:**
```rust
#[wire_state("submit_form")]
fn submit() {
    let result = api_call();  // Returns Result
    // ⚠️ ERROR: Unhandled error path
    // Path to success state exists
    // Path to error state is blocked
}
```

```rust
#[wire_state("load_data")]
async fn load() {
    let data = fetch_data();  // Returns Future
    // ⚠️ ERROR: Missing .await
    // Path exists but data is never resolved
}
```

```rust
#[wire_state("update_profile")]
fn update(user: &mut User) {
    user.name = new_name;
    // ⚠️ WARNING: Partial update
    // email field never set
    // Path to success but data incomplete
}
```

### Tier 3: Data Flow Verification

For critical paths, tRust proves data actually flows:

```rust
#[wire_state("process_payment")]
#[wire_data_flow("card_number=>payment_processor")]
fn process(card: CardInfo) {
    let processor = get_processor();
    // tRust PROVES: card.number reaches processor.charge()
    // Not just that the function is called
    // But that the actual data flows through
}
```

This catches:
- Values read but never used
- Outputs computed but never returned
- Side effects intended but not triggered

---

## How It Works

### MIR-Level Analysis

tRust has full access to Rust's MIR (Mid-level Intermediate Representation):

```
Source → HIR → MIR → LLVM IR → Binary
              ↑
         tRust wiring
         analysis here
```

At MIR level:
- All syntactic sugar is gone
- Control flow is explicit
- Function calls are resolved
- Monomorphization is complete

This gives us:
- **Exact call graph** - no guessing which function is called
- **Precise control flow** - every branch, every loop
- **Type-resolved generics** - `Vec<User>` not `Vec<T>`
- **Inlined closures** - actual code, not opaque functions

### Path Enumeration

For annotated states, tRust:

1. **Builds the call graph** from `#[wire_start]`
2. **Finds all paths** to each `#[wire_state]`
3. **Analyzes each path** for anomalies
4. **Proves or disproves** `#[wire_must_reach]` assertions
5. **Reports** unreachable states, anomalous paths, data flow gaps

### Bounded Analysis

Full path enumeration is undecidable. tRust uses:

- **Bounded model checking** - analyze up to N iterations
- **Abstract interpretation** - over-approximate when needed
- **User hints** - `#[wire_bound(iterations = 100)]` (planned)
- **Incremental checking** - only re-analyze changed components

---

## Integration with tRust Verification

Wiring verification complements specification verification:

| Specification | Wiring |
|--------------|--------|
| Proves *what* functions do | Proves functions *are called* |
| Local to each function | Global across the application |
| "sort() returns sorted list" | "sort() is reachable from UI" |
| Functional correctness | Structural correctness |

Together they guarantee:
1. Each component is correct (specs)
2. Components are connected (wiring)
3. The system works end-to-end (composition)

---

## AI Workflow

### AI Writes Specs + Wiring Annotations

```rust
// AI generates both the code AND the annotations
#[wire_state("user_dashboard")]
#[wire_must_reach("settings, logout, notifications")]
#[requires("user.is_authenticated")]
#[ensures("ui.current_view == View::Dashboard")]
fn show_dashboard(user: AuthenticatedUser) -> View {
    // Implementation
}
```

The AI declares:
- What states exist (`#[wire_state]`)
- What states must be reachable (`#[wire_must_reach]`)
- What preconditions must hold (`#[requires]`)
- What postconditions are guaranteed (`#[ensures]`)

### tRust Verifies Everything

```
┌─────────────────────────────────────────────────────────┐
│                    AI generates code                     │
└─────────────────────────┬───────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────┐
│                    tRust compiler                        │
│  ┌─────────────────────────────────────────────────┐   │
│  │  1. Type checking (standard Rust)               │   │
│  │  2. Specification verification (SMT proofs)     │   │
│  │  3. Wiring verification (path analysis)         │   │
│  │  4. Memory safety (existing Rust guarantees)    │   │
│  └─────────────────────────────────────────────────┘   │
└─────────────────────────┬───────────────────────────────┘
                          │
            ┌─────────────┴─────────────┐
            │                           │
            ▼                           ▼
    ┌──────────────┐           ┌──────────────┐
    │   VERIFIED   │           │   REJECTED   │
    │   Execute    │           │   Fix + Retry│
    └──────────────┘           └──────────────┘
```

### Counterexamples Guide Fixes

When wiring verification fails:

```
error[W001]: Unreachable state
  --> src/app.rs:45:1
   |
45 | #[wire_state("payment_success")]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: No path found from #[wire_start] to this state
   = help: Missing connection from checkout flow

   Nearest reachable states:
     - "checkout" at src/checkout.rs:12
     - "cart" at src/cart.rs:8

   Possible fix: Add call to payment_success() from checkout flow
```

The error tells the AI exactly:
- What state is unreachable
- What states ARE reachable nearby
- How to fix it

---

## Example: E-Commerce Application

```rust
#[wire_start]
fn main() {
    let app = Router::new()
        .route("/", get(home))
        .route("/product/:id", get(product_page))
        .route("/cart", get(cart_page).post(add_to_cart))
        .route("/checkout", post(begin_checkout))
        .route("/payment", post(process_payment));

    Server::bind(app).run()
}

#[wire_state("home")]
async fn home() -> Html { ... }

#[wire_state("product_view")]
#[wire_must_reach("cart")]  // User can add to cart
async fn product_page(id: ProductId) -> Html { ... }

#[wire_state("cart")]
#[wire_must_reach("checkout")]  // User can checkout
async fn cart_page(session: Session) -> Html { ... }

#[wire_state("checkout")]
#[wire_must_reach("payment_success, payment_error")]
async fn begin_checkout(cart: Cart) -> Html { ... }

#[wire_state("payment_success")]
async fn payment_confirmed(receipt: Receipt) -> Html { ... }

#[wire_state("payment_error")]
#[wire_recoverable]  // Can retry or return to cart
async fn payment_failed(error: Error) -> Html { ... }
```

**tRust verifies:**
1. ✓ All states reachable from `main()`
2. ✓ `product_view` → `cart` path exists (via add_to_cart)
3. ✓ `cart` → `checkout` path exists
4. ✓ `checkout` → `payment_success` and `payment_error` paths exist
5. ✓ `payment_error` has recovery path (back to cart)

**If any path is missing, compilation fails.**

---

## Why This Matters

### For AI Code Generation

The AI can't "forget" to wire things together. The compiler enforces connectivity.

### For Large Systems

As systems grow, wiring complexity explodes. Manual tracking is impossible. Formal verification scales.

### For Runtime Code Generation

When AI generates code at runtime, there's no time for manual review. The compiler must catch wiring bugs instantly.

### For Correctness Guarantees

Tests only check exercised paths. Wiring verification proves ALL paths exist.

---

## Implementation Status

Wiring verification is **implemented** in tRust (see ROADMAP.md Phase 6.5):

- [x] Annotation syntax (`#[wire_start]`, `#[wire_state]`, `#[wire_must_reach]`, `#[wire_recoverable]`, `#[wire_data_flow]`, `#[wire_terminal]`)
- [x] MIR-level call graph extraction (`CallGraph` in `rustc_vc/src/wiring.rs`)
- [x] Reachability analysis (BFS from start functions)
- [x] Monomorphized generic tracking (`generic_args` in `Terminator::Call`)
- [x] Closure and function pointer tracking (`MirType::Closure`, `IndirectCall`)
- [x] Async/.await chain analysis (`AsyncChainAnalyzer`)
- [x] Path anomaly detection:
  - [x] Unhandled `Result` error paths (`ResultAnalyzer`)
  - [x] Missing `.await` on futures (`AwaitAnalyzer`)
  - [x] Partial struct updates (`StructUpdateAnalyzer`)
  - [x] Dead code paths (`PathAnomaly::DeadCode`)
- [x] Data flow tracking (`DataFlowAnalyzer`)
- [x] Integration with specification verification (`verify_crate` pipeline)
- [ ] Incremental checking (future)
- [ ] IDE integration (future)

**Test Coverage:**
- 63 unit tests for wiring verification in `rustc_vc`
- Integration tests: `wire_test.rs`, `path_anomaly_test.rs`, `async_chain_test.rs`

**External Integration (Phase 6.5.6):**
The [tla-wire](https://github.com/dropbox/tla2) project provides complementary functionality:
- Language-agnostic graph extraction
- Path analysis algorithms
- Cross-language wiring analysis (Rust + TypeScript)

Integration with tla-wire is planned for future work.
