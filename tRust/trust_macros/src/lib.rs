//! tRust Specification Macros
//!
//! Procedural macros for verification specifications in tRust.
//!
//! # Supported Attributes
//!
//! - `#[requires(expr)]` - Function precondition
//! - `#[ensures(expr)]` - Function postcondition
//! - `#[api(...)]` - HTTP endpoint metadata for contract export
//! - `#[invariant(expr)]` - Loop invariant
//! - `#[decreases(expr)]` - Termination measure
//! - `#[ghost]` - Ghost function (erased at runtime)
//! - `#[trusted]` - Function is trusted (not verified)
//! - `#[pure]` - Function has no side effects
//! - `#[effects(...)]` - Declare allowed effects (IO/Alloc/Panic)
//! - `#[trust_level(level)]` - Set trust level for a module
//!
//! # Wiring Attributes (Phase 6.5)
//!
//! - `#[wire(start)]` - Entry point for reachability analysis
//! - `#[wire(state = "name")]` - Named reachable state
//! - `#[wire(must_reach = "state")]` - Required successor state
//! - `#[wire(recoverable)]` - Error state with recovery path
//!
//! # Trust Levels
//!
//! - `verified` - All specs must be proven; failures are compile errors
//! - `assumed` - No verification performed (default for legacy code)
//! - `audited` - Specs trusted without machine verification
//! - `verified_warn` - Specs proven but failures are warnings
//!
//! # Specification Expression Syntax
//!
//! Specifications are Rust expressions extended with:
//! - `result` - The return value (in ensures)
//! - `old(expr)` - Value of expr at function entry (in ensures)
//! - `forall |x: T| pred` - Universal quantification
//! - `exists |x: T| pred` - Existential quantification
//! - `a => b` - Implication (desugared to `!a || b`)

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    Expr, Ident, ItemFn, Result, Token,
};

mod spec_expr;

use spec_expr::SpecExpr;

/// Specification content parsed from attribute
struct SpecContent {
    expr: SpecExpr,
}

impl Parse for SpecContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let expr = SpecExpr::parse(input)?;
        Ok(Self { expr })
    }
}

/// Decreases clause (termination measure)
struct DecreasesContent {
    measures: Punctuated<Expr, Token![,]>,
}

impl Parse for DecreasesContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let measures = Punctuated::parse_separated_nonempty(input)?;
        Ok(Self { measures })
    }
}

/// Generate a hidden attribute to preserve spec metadata
fn spec_attribute(kind: &str, content: &impl ToTokens) -> TokenStream2 {
    let content_str = content.to_token_stream().to_string();
    quote! {
        #[doc(hidden)]
        #[allow(unused_attributes)]
        #[cfg_attr(trust_verify, trust_spec(#kind = #content_str))]
    }
}

/// `#[requires(expr)]` - Function precondition
///
/// # Example
/// ```ignore
/// #[requires(x > 0)]
/// fn sqrt(x: f64) -> f64 { ... }
/// ```
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as SpecContent);
    let input = parse_macro_input!(item as ItemFn);

    let spec_attr = spec_attribute("requires", &content.expr);
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// `#[ensures(expr)]` - Function postcondition
///
/// # Example
/// ```ignore
/// #[ensures(result >= 0.0)]
/// fn abs(x: f64) -> f64 { ... }
/// ```
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as SpecContent);
    let input = parse_macro_input!(item as ItemFn);

    let spec_attr = spec_attribute("ensures", &content.expr);
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// `#[api(...)]` - HTTP endpoint metadata for contract export (Phase 6.5.6)
///
/// Stores the raw argument tokens as metadata for the compiler's verification pass.
///
/// # Examples
/// ```ignore
/// #[api(path = "/api/users", method = "POST")]
/// #[api("/api/users", "POST")]
/// fn create_user(...) { ... }
/// ```
#[proc_macro_attribute]
pub fn api(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args: TokenStream2 = attr.into();
    let input = parse_macro_input!(item as ItemFn);

    let spec_attr = spec_attribute("api", &args);
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// `#[invariant(expr)]` - Loop invariant
///
/// Applied to while/for/loop statements.
///
/// # Example
/// ```ignore
/// #[invariant(i <= arr.len())]
/// while i < arr.len() { ... }
/// ```
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as SpecContent);
    let input: TokenStream2 = item.into();

    // For now, pass through - full loop support needs compiler integration
    let spec_attr = spec_attribute("invariant", &content.expr);
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// `#[decreases(expr)]` - Termination measure
///
/// Specifies a value that decreases with each iteration/recursion.
///
/// # Example
/// ```ignore
/// #[decreases(n)]
/// fn factorial(n: u64) -> u64 { ... }
/// ```
#[proc_macro_attribute]
pub fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as DecreasesContent);
    let input: TokenStream2 = item.into();

    let measures: Vec<_> = content.measures.iter().collect();
    let spec_attr = spec_attribute("decreases", &quote! { (#(#measures),*) });
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// `#[ghost]` - Ghost function
///
/// Marks a function as ghost code - used only in specifications,
/// erased at runtime.
///
/// # Example
/// ```ignore
/// #[ghost]
/// fn permutation<T>(a: &[T], b: &[T]) -> bool { ... }
/// ```
#[proc_macro_attribute]
pub fn ghost(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    // Ghost functions are removed in release builds
    let output = quote! {
        #[doc(hidden)]
        #[allow(dead_code)]
        #[cfg(any(trust_verify, debug_assertions))]
        #input
    };

    output.into()
}

/// `#[trusted]` - Trusted function
///
/// Marks a function as trusted - its spec is assumed, not verified.
/// Use for FFI, unsafe code, or well-known correct implementations.
///
/// # Example
/// ```ignore
/// #[trusted]
/// #[ensures(result.len() == cap)]
/// fn allocate(cap: usize) -> Vec<u8> { ... }
/// ```
#[proc_macro_attribute]
pub fn trusted(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(trusted = "true"))]
        #input
    };

    output.into()
}

/// `#[pure]` - Pure function
///
/// Marks a function as pure (no side effects).
/// Pure functions can be used freely in specifications.
///
/// # Example
/// ```ignore
/// #[pure]
/// fn len<T>(v: &Vec<T>) -> usize { v.len() }
/// ```
#[proc_macro_attribute]
pub fn pure(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(pure = "true"))]
        #input
    };

    output.into()
}

/// `#[pure_returns("expr")]` - Pure function return expression
///
/// Declares what expression a pure function returns. Used for method inlining
/// in specifications. When specs contain `x.method()`, the verifier can substitute
/// the `pure_returns` expression with `self` replaced by `x`.
///
/// # Example
/// ```ignore
/// impl Wrap {
///     #[pure]
///     #[pure_returns("self.0")]
///     fn get(&self) -> usize { self.0 }
/// }
///
/// // Now specs can use result.get() and it will be inlined to result.0
/// #[ensures("result.get() == 42")]
/// fn make_wrap() -> Wrap { Wrap(42) }
/// ```
#[proc_macro_attribute]
pub fn pure_returns(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let expr = attr.to_string();
    // Remove quotes if present
    let expr = expr.trim_matches('"').to_string();

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(pure_returns = #expr))]
        #input
    };

    output.into()
}

/// `#[may_diverge]` - May not terminate
///
/// Indicates a function may not terminate (loops forever, panics).
/// Disables termination checking for this function.
#[proc_macro_attribute]
pub fn may_diverge(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(may_diverge = "true"))]
        #input
    };

    output.into()
}

/// `#[effects(...)]` / `#[effect(...)]` - Declare allowed effects
///
/// Effects are a Phase 5 (Effects and Purity) feature. The verifier uses this
/// metadata to ensure the caller's allowed effect set includes the callee's
/// effects.
///
/// # Example
/// ```ignore
/// #[effects(Alloc, Panic)]
/// fn allocate_or_panic(n: usize) -> Vec<u8> { ... }
/// ```
struct EffectsContent {
    effects: Punctuated<Ident, Token![,]>,
}

impl Parse for EffectsContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let effects = Punctuated::parse_terminated(input)?;
        Ok(Self { effects })
    }
}

#[proc_macro_attribute]
pub fn effects(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as EffectsContent);
    let input = parse_macro_input!(item as ItemFn);

    let effects = content.effects.iter();
    let spec_attr = spec_attribute("effects", &quote! { #(#effects),* });
    let output = quote! {
        #spec_attr
        #input
    };

    output.into()
}

/// Alias for `#[effects(...)]`
#[proc_macro_attribute]
pub fn effect(attr: TokenStream, item: TokenStream) -> TokenStream {
    effects(attr, item)
}

/// Trust level content
struct TrustLevelContent {
    level: syn::Ident,
}

impl Parse for TrustLevelContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let level: syn::Ident = input.parse()?;
        Ok(Self { level })
    }
}

/// `#[trust_level(level)]` - Set trust level for a module
///
/// Sets the trust level for all functions in the annotated module.
///
/// # Trust Levels
///
/// - `verified` - All specs must be proven; failures are compile errors
/// - `assumed` - No verification performed (default)
/// - `audited` - Specs trusted without machine verification
/// - `verified_warn` - Specs proven but failures are warnings
///
/// # Example
/// ```ignore
/// #[trust_level(verified)]
/// mod verified_module {
///     #[requires(x > 0)]
///     #[ensures(result >= 1)]
///     fn sqrt(x: u64) -> u64 { ... }
/// }
///
/// #[trust_level(assumed)]
/// mod legacy_code {
///     // No verification performed
///     fn old_function() { ... }
/// }
/// ```
#[proc_macro_attribute]
pub fn trust_level(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as TrustLevelContent);
    let input: TokenStream2 = item.into();

    let level_str = content.level.to_string().to_lowercase();

    // Validate trust level
    let valid_levels = ["verified", "assumed", "audited", "verified_warn"];
    if !valid_levels.contains(&level_str.as_str()) {
        let msg = format!(
            "invalid trust level '{}'. Expected one of: {}",
            level_str,
            valid_levels.join(", ")
        );
        return syn::Error::new(content.level.span(), msg)
            .to_compile_error()
            .into();
    }

    // Emit cfg attributes for the trust level
    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(trust_level = #level_str))]
        #input
    };

    output.into()
}

// ============================================================================
// Wire Attributes (Phase 6.5 - Wiring Verification)
// ============================================================================

/// Wire attribute content - supports multiple wire specifications
enum WireKind {
    /// Entry point for reachability analysis
    Start,
    /// Named reachable state
    State(String),
    /// Required successor state(s)
    MustReach(Vec<String>),
    /// Error state with recovery path
    Recoverable,
    /// Data flow annotation (input -> output)
    DataFlow { input: String, output: String },
}

struct WireContent {
    kinds: Vec<WireKind>,
}

impl Parse for WireContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut kinds = Vec::new();

        loop {
            let ident: Ident = input.parse()?;
            let ident_str = ident.to_string();

            match ident_str.as_str() {
                "start" => kinds.push(WireKind::Start),
                "recoverable" => kinds.push(WireKind::Recoverable),
                "state" => {
                    let _: Token![=] = input.parse()?;
                    let lit: syn::LitStr = input.parse()?;
                    kinds.push(WireKind::State(lit.value()));
                }
                "must_reach" => {
                    let _: Token![=] = input.parse()?;
                    // Can be a single string or array of strings
                    if input.peek(syn::token::Bracket) {
                        let content;
                        syn::bracketed!(content in input);
                        let states: Punctuated<syn::LitStr, Token![,]> =
                            Punctuated::parse_terminated(&content)?;
                        kinds.push(WireKind::MustReach(
                            states.into_iter().map(|s| s.value()).collect(),
                        ));
                    } else {
                        let lit: syn::LitStr = input.parse()?;
                        kinds.push(WireKind::MustReach(vec![lit.value()]));
                    }
                }
                "data_flow" => {
                    // Parse data_flow(input, output)
                    let content;
                    syn::parenthesized!(content in input);
                    let input_name: Ident = content.parse()?;
                    let _: Token![,] = content.parse()?;
                    let output_name: Ident = content.parse()?;
                    kinds.push(WireKind::DataFlow {
                        input: input_name.to_string(),
                        output: output_name.to_string(),
                    });
                }
                _ => {
                    return Err(syn::Error::new(
                        ident.span(),
                        format!(
                            "unknown wire attribute '{ident_str}'. Expected: start, state, must_reach, recoverable, data_flow"
                        ),
                    ));
                }
            }

            if input.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            } else {
                break;
            }
        }

        Ok(Self { kinds })
    }
}

/// `#[wire(...)]` - Wiring verification attributes
///
/// Marks functions for structural connectivity verification.
/// The compiler proves that code paths exist from entry points through
/// all annotated states.
///
/// # Variants
///
/// - `#[wire(start)]` - Entry point (e.g., main, route handler)
/// - `#[wire(state = "name")]` - Named reachable state
/// - `#[wire(must_reach = "state")]` - Must be able to reach this state
/// - `#[wire(must_reach = ["s1", "s2"])]` - Must reach all listed states
/// - `#[wire(recoverable)]` - Error state with recovery path
/// - `#[wire(data_flow(input, output))]` - Data must flow from input to output
///
/// # Example
///
/// ```ignore
/// #[wire(start)]
/// fn main() {
///     Router::new().route("/checkout", post(checkout)).run()
/// }
///
/// #[wire(state = "checkout", must_reach = ["payment_success", "payment_error"])]
/// async fn checkout(cart: Cart) -> Response { ... }
///
/// #[wire(state = "payment_success")]
/// async fn confirmed(receipt: Receipt) -> Response { ... }
///
/// #[wire(state = "payment_error", recoverable)]
/// async fn failed(err: Error) -> Response { ... }
/// ```
#[proc_macro_attribute]
pub fn wire(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as WireContent);
    let input = parse_macro_input!(item as ItemFn);

    let mut attrs = Vec::new();

    for kind in content.kinds {
        match kind {
            WireKind::Start => {
                attrs.push(quote! {
                    #[doc(hidden)]
                    #[cfg_attr(trust_verify, trust_spec(wire_start = "true"))]
                });
            }
            WireKind::State(name) => {
                attrs.push(quote! {
                    #[doc(hidden)]
                    #[cfg_attr(trust_verify, trust_spec(wire_state = #name))]
                });
            }
            WireKind::MustReach(states) => {
                let states_str = states.join(",");
                attrs.push(quote! {
                    #[doc(hidden)]
                    #[cfg_attr(trust_verify, trust_spec(wire_must_reach = #states_str))]
                });
            }
            WireKind::Recoverable => {
                attrs.push(quote! {
                    #[doc(hidden)]
                    #[cfg_attr(trust_verify, trust_spec(wire_recoverable = "true"))]
                });
            }
            WireKind::DataFlow { input, output } => {
                let flow_str = format!("{input}=>{output}");
                attrs.push(quote! {
                    #[doc(hidden)]
                    #[cfg_attr(trust_verify, trust_spec(wire_data_flow = #flow_str))]
                });
            }
        }
    }

    let output = quote! {
        #(#attrs)*
        #input
    };

    output.into()
}

// ============================================================================
// Protocol Module Attributes (Phase 6.3 - Protocol Verification)
// ============================================================================

/// Protocol attribute content
struct ProtocolContent {
    name: Option<String>,
}

impl Parse for ProtocolContent {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Ok(Self { name: None });
        }

        // Parse name = "..."
        let ident: Ident = input.parse()?;
        if ident != "name" {
            return Err(syn::Error::new(
                ident.span(),
                format!("expected 'name', found '{ident}'"),
            ));
        }
        let _: Token![=] = input.parse()?;
        let lit: syn::LitStr = input.parse()?;
        Ok(Self {
            name: Some(lit.value()),
        })
    }
}

/// `#[protocol]` / `#[protocol(name = "...")]` - Define a protocol module
///
/// Marks a module as a protocol specification. Inside the module:
/// - Functions marked `#[init]` define the initial state
/// - Functions marked `#[action]` define state transitions
/// - Functions marked `#[safety]` define invariants (□P)
/// - Functions marked `#[liveness]` define progress properties (◇P)
/// - Functions marked `#[weak_fairness]` or `#[strong_fairness]` define fairness conditions
/// - Structs define state variables
///
/// # Example
///
/// ```ignore
/// #[protocol(name = "Counter")]
/// mod counter {
///     struct State {
///         count: i32,
///     }
///
///     #[init]
///     fn init() -> State {
///         State { count: 0 }
///     }
///
///     #[action]
///     fn increment(state: &mut State) {
///         state.count += 1;
///     }
///
///     #[safety]
///     fn count_non_negative(state: &State) -> bool {
///         state.count >= 0
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn protocol(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as ProtocolContent);
    let input: TokenStream2 = item.into();

    let name_attr = if let Some(name) = content.name {
        quote! {
            #[doc(hidden)]
            #[cfg_attr(trust_verify, trust_spec(protocol_name = #name))]
        }
    } else {
        quote! {
            #[doc(hidden)]
            #[cfg_attr(trust_verify, trust_spec(protocol = "true"))]
        }
    };

    let output = quote! {
        #name_attr
        #input
    };

    output.into()
}

/// `#[init]` - Define the initial state predicate for a protocol
///
/// The function should return the initial state values.
///
/// # Example
/// ```ignore
/// #[init]
/// fn init() -> State {
///     State { x: 0, y: 0 }
/// }
/// ```
#[proc_macro_attribute]
pub fn init(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(protocol_init = "true"))]
        #input
    };

    output.into()
}

/// `#[action]` / `#[action(name = "...")]` - Define a protocol action
///
/// Actions define state transitions. The function takes the current state
/// and optionally returns the new state or modifies it in place.
///
/// # Example
/// ```ignore
/// #[action]
/// fn send(state: &mut State, msg: Message) {
///     state.queue.push(msg);
/// }
/// ```
struct ActionContent {
    name: Option<String>,
}

impl Parse for ActionContent {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Ok(Self { name: None });
        }

        let ident: Ident = input.parse()?;
        if ident != "name" {
            return Err(syn::Error::new(
                ident.span(),
                format!("expected 'name', found '{ident}'"),
            ));
        }
        let _: Token![=] = input.parse()?;
        let lit: syn::LitStr = input.parse()?;
        Ok(Self {
            name: Some(lit.value()),
        })
    }
}

#[proc_macro_attribute]
pub fn action(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as ActionContent);
    let input = parse_macro_input!(item as ItemFn);

    let action_attr = if let Some(name) = content.name {
        quote! {
            #[doc(hidden)]
            #[cfg_attr(trust_verify, trust_spec(protocol_action = #name))]
        }
    } else {
        quote! {
            #[doc(hidden)]
            #[cfg_attr(trust_verify, trust_spec(protocol_action = "true"))]
        }
    };

    let output = quote! {
        #action_attr
        #input
    };

    output.into()
}

/// `#[safety]` - Define a safety property (invariant)
///
/// Safety properties must hold in all reachable states: □P (always P).
/// The function should return a boolean indicating whether the property holds.
///
/// # Example
/// ```ignore
/// #[safety]
/// fn mutex_exclusion(state: &State) -> bool {
///     !(state.in_critical_a && state.in_critical_b)
/// }
/// ```
#[proc_macro_attribute]
pub fn safety(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(protocol_safety = "true"))]
        #input
    };

    output.into()
}

/// `#[liveness]` - Define a liveness property
///
/// Liveness properties state that something good eventually happens: ◇P (eventually P).
/// The function should return a boolean indicating the "good" condition.
///
/// # Example
/// ```ignore
/// #[liveness]
/// fn eventually_delivered(state: &State) -> bool {
///     state.delivered
/// }
/// ```
#[proc_macro_attribute]
pub fn liveness(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(protocol_liveness = "true"))]
        #input
    };

    output.into()
}

/// `#[weak_fairness(action)]` - Weak fairness condition
///
/// Weak fairness for action A: if A is continuously enabled, it eventually occurs.
/// WF(A) = □◇¬enabled(A) ∨ □◇A
///
/// # Example
/// ```ignore
/// #[weak_fairness(send)]
/// fn wf_send() {}
/// ```
struct FairnessContent {
    action: Ident,
}

impl Parse for FairnessContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let action: Ident = input.parse()?;
        Ok(Self { action })
    }
}

#[proc_macro_attribute]
pub fn weak_fairness(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as FairnessContent);
    let input: TokenStream2 = item.into();

    let action_name = content.action.to_string();
    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(weak_fairness = #action_name))]
        #input
    };

    output.into()
}

/// `#[strong_fairness(action)]` - Strong fairness condition
///
/// Strong fairness for action A: if A is infinitely often enabled, it eventually occurs.
/// SF(A) = ◇□¬enabled(A) ∨ □◇A
///
/// # Example
/// ```ignore
/// #[strong_fairness(receive)]
/// fn sf_receive() {}
/// ```
#[proc_macro_attribute]
pub fn strong_fairness(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as FairnessContent);
    let input: TokenStream2 = item.into();

    let action_name = content.action.to_string();
    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(strong_fairness = #action_name))]
        #input
    };

    output.into()
}

/// `#[party]` - Define a party/role in a multi-party protocol
///
/// # Example
/// ```ignore
/// #[protocol]
/// mod distributed {
///     #[party]
///     mod client {
///         #[action]
///         fn send_request() { ... }
///     }
///
///     #[party]
///     mod server {
///         #[action]
///         fn handle_request() { ... }
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn party(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input: TokenStream2 = item.into();

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(protocol_party = "true"))]
        #input
    };

    output.into()
}

/// `#[message]` - Define a message type for inter-party communication
///
/// # Example
/// ```ignore
/// #[message(from = "client", to = "server")]
/// struct Request {
///     payload: Vec<u8>,
/// }
/// ```
struct MessageContent {
    from: String,
    to: String,
}

impl Parse for MessageContent {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut from = None;
        let mut to = None;

        while !input.is_empty() {
            let ident: Ident = input.parse()?;
            let _: Token![=] = input.parse()?;
            let lit: syn::LitStr = input.parse()?;

            if ident == "from" {
                from = Some(lit.value());
            } else if ident == "to" {
                to = Some(lit.value());
            } else {
                return Err(syn::Error::new(
                    ident.span(),
                    format!("expected 'from' or 'to', found '{ident}'"),
                ));
            }

            if input.peek(Token![,]) {
                let _: Token![,] = input.parse()?;
            }
        }

        Ok(Self {
            from: from.unwrap_or_default(),
            to: to.unwrap_or_default(),
        })
    }
}

#[proc_macro_attribute]
pub fn message(attr: TokenStream, item: TokenStream) -> TokenStream {
    let content = parse_macro_input!(attr as MessageContent);
    let input: TokenStream2 = item.into();

    let from = &content.from;
    let to = &content.to;
    let msg_spec = format!("{from}=>{to}");

    let output = quote! {
        #[doc(hidden)]
        #[cfg_attr(trust_verify, trust_spec(protocol_message = #msg_spec))]
        #input
    };

    output.into()
}
