//! TLA2 State Machine Extraction from Rust Async Code
//!
//! This crate extracts state machines from async Rust functions and converts them
//! to the TLA2Model format for temporal property verification.
//!
//! # Architecture
//!
//! ```text
//! AsyncStateMachine (vc_ir)  ->  TLA2Model  ->  JSON/TLA+ Output
//!        ^                          ^                ^
//!        |                          |                |
//!   Extracted from             Portable         For TLA2 CLI
//!   MIR by rustc_vc            format           or TLC checker
//!
//! MIR State Machine  ->  TLA2Model  ->  TLA+ Specification
//!        ^                   ^                 ^
//!        |                   |                 |
//!   Phase 4 extraction   Phase 5         Actual .tla file
//!   (basic blocks)       conversion      for model checking
//! ```
//!
//! # Usage
//!
//! ## From vc_ir AsyncStateMachine
//! ```rust,ignore
//! use tla_extract::{TLA2Model, convert_to_tla2};
//! use vc_ir::temporal::AsyncStateMachine;
//!
//! let sm: AsyncStateMachine = /* extracted from compiler */;
//! let model = convert_to_tla2(&sm);
//! let json = model.to_json();
//! ```
//!
//! ## From MIR extraction (Phase 5)
//! ```rust,ignore
//! use tla_extract::{MirStateMachineResult, convert_mir_to_tla2, generate_tla2_spec};
//!
//! let mir: MirStateMachineResult = /* from rustc_verify */;
//! let model = convert_mir_to_tla2(&mir);
//! let tla_spec = generate_tla2_spec(&model);
//! // Write to .tla file for TLC model checker
//! ```

mod convert;
mod mir_convert;
mod model;
mod tla2_spec;

pub use convert::*;
pub use mir_convert::*;
pub use model::*;
pub use tla2_spec::*;

/// Version of the TLA2 export format
pub const TLA2_EXPORT_VERSION: &str = "1.0";

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::temporal::{AsyncStateKind, AsyncStateMachine};

    #[test]
    fn test_simple_conversion() {
        // Create a simple async state machine
        let mut sm = AsyncStateMachine::new("test_async");
        let s1 = sm.add_state("Suspended", AsyncStateKind::Suspended);
        let s2 = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_yield_point(0, s1);

        // Convert to TLA2Model
        let model = convert_to_tla2(&sm);

        assert_eq!(model.name, "test_async");
        assert_eq!(model.transitions.len(), 2);
        assert_eq!(model.initial_state, StateId(0));
    }

    #[test]
    fn test_json_output() {
        let mut sm = AsyncStateMachine::new("json_test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let model = convert_to_tla2(&sm);
        let json = model.to_json();

        assert!(json.contains("\"name\": \"json_test\""));
        assert!(json.contains("\"version\": \"1.0\""));
    }

    #[test]
    fn test_branching_state_machine() {
        let mut sm = AsyncStateMachine::new("branching");
        let branch_a = sm.add_state("BranchA", AsyncStateKind::Suspended);
        let branch_b = sm.add_state("BranchB", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);

        // Start branches to A and B
        sm.add_transition(0, branch_a);
        sm.add_transition(0, branch_b);
        // Both branches to End
        sm.add_transition(branch_a, end);
        sm.add_transition(branch_b, end);

        let model = convert_to_tla2(&sm);

        assert_eq!(model.transitions.len(), 4);
        assert_eq!(model.terminal_states.len(), 1);
    }

    /// Integration test: Full MIR to TLA+ specification pipeline (Phase 5)
    #[test]
    fn test_mir_to_tla2_spec_integration() {
        // Create a realistic MIR state machine (simulating async fn with await)
        let mir = MirStateMachineResult {
            name: "async_with_await".to_string(),
            blocks: vec![
                // Block 0: Entry
                MirBasicBlockInfo {
                    index: 0,
                    terminator_kind: "Call".to_string(),
                    successors: vec![1, 2],
                    is_yield: false,
                    guard: Some("poll_result == 0".to_string()),
                    statement_count: 2,
                },
                // Block 1: Ready (poll returned Ready)
                MirBasicBlockInfo {
                    index: 1,
                    terminator_kind: "Goto".to_string(),
                    successors: vec![3],
                    is_yield: false,
                    guard: None,
                    statement_count: 1,
                },
                // Block 2: Pending (poll returned Pending, yield)
                MirBasicBlockInfo {
                    index: 2,
                    terminator_kind: "SwitchInt".to_string(),
                    successors: vec![0],
                    is_yield: true,
                    guard: Some("state: 0".to_string()),
                    statement_count: 0,
                },
                // Block 3: Return
                MirBasicBlockInfo {
                    index: 3,
                    terminator_kind: "Return".to_string(),
                    successors: vec![],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
            ],
            yield_points: vec![MirYieldPoint {
                block: 2,
                resume_block: 0,
                drop_block: None,
                yielded_type: "()".to_string(),
            }],
            captured_vars: vec![MirCapturedVar {
                name: "counter".to_string(),
                ty: "i32".to_string(),
                is_mut: true,
            }],
            state_count: 4,
            transition_count: 4,
        };

        // Phase 5: Convert MIR to TLA2Model
        let model = convert_mir_to_tla2(&mir);

        // Verify model structure
        assert_eq!(model.name, "async_with_await");
        // counter, _state, _pc
        assert_eq!(model.variables.len(), 3);
        assert_eq!(model.variables[0].name, "counter");
        assert_eq!(model.transitions.len(), 4);
        assert_eq!(model.terminal_states.len(), 1);
        assert_eq!(model.terminal_states[0], StateId(3));

        // Phase 5: Generate TLA+ specification
        let tla_spec = generate_tla2_spec(&model);

        // Verify TLA+ spec structure
        assert!(tla_spec.contains("---- MODULE async_with_await ----"));
        assert!(tla_spec.contains("EXTENDS Integers"));
        assert!(tla_spec.contains("VARIABLES counter, _state, _pc"));
        assert!(tla_spec.contains("Init =="));
        assert!(tla_spec.contains("Next =="));
        assert!(tla_spec.contains("Spec == Init /\\ [][Next]_vars"));
        assert!(tla_spec.contains("TypeInvariant =="));
        assert!(tla_spec.contains("NoDeadlock =="));
        assert!(tla_spec.contains("===="));

        // Verify transitions are included
        assert!(tla_spec.contains("call_0_to_1"));
        assert!(tla_spec.contains("call_0_to_2"));

        // Generate config
        let cfg = generate_tla2_config(&model);
        assert!(cfg.contains("SPECIFICATION Spec"));
        assert!(cfg.contains("INVARIANT TypeInvariant"));
    }

    /// Test that TLA+ spec output is syntactically valid
    #[test]
    fn test_tla2_spec_syntax() {
        let mir = MirStateMachineResult {
            name: "simple".to_string(),
            blocks: vec![
                MirBasicBlockInfo {
                    index: 0,
                    terminator_kind: "Goto".to_string(),
                    successors: vec![1],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
                MirBasicBlockInfo {
                    index: 1,
                    terminator_kind: "Return".to_string(),
                    successors: vec![],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
            ],
            yield_points: vec![],
            captured_vars: vec![],
            state_count: 2,
            transition_count: 1,
        };

        let model = convert_mir_to_tla2(&mir);
        let spec = generate_tla2_spec(&model);

        // Check for balanced module delimiters
        assert!(spec.starts_with("---- MODULE simple ----"));
        assert!(spec.ends_with("====\n"));

        // Check for required TLA+ keywords
        assert!(spec.contains("EXTENDS"));
        assert!(spec.contains("VARIABLES"));
        assert!(spec.contains("Init"));
        assert!(spec.contains("Next"));
        assert!(spec.contains("Spec"));

        // Check for proper TLA+ operators
        assert!(spec.contains("/\\")); // AND
        assert!(spec.contains("[]")); // always (in Spec)
        assert!(spec.contains('_')); // subscript (in Spec)
    }
}
