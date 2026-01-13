//! TLA2 Test Case: Two-Mutex Deadlock
//!
//! This test case demonstrates the classic deadlock scenario where two processes
//! attempt to acquire two mutexes in opposite order, leading to potential deadlock.
//!
//! Process A: lock(mutex1) -> lock(mutex2) -> unlock(mutex2) -> unlock(mutex1)
//! Process B: lock(mutex2) -> lock(mutex1) -> unlock(mutex1) -> unlock(mutex2)
//!
//! Expected: TLA2 should find a counterexample showing the deadlock state where:
//! - Process A holds mutex1, waiting for mutex2
//! - Process B holds mutex2, waiting for mutex1
//!
//! This is a canonical test case for validating temporal model checkers.
//!
//! Expected: PASS (compile and run as specification)

#![feature(rustc_attrs)]

// ============================================
// State Machine Representation
// ============================================

/// Process state enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ProcessState {
    Start = 0,        // Initial state
    HoldFirst = 1,    // Holds first mutex, trying second
    HoldBoth = 2,     // Holds both mutexes
    Done = 3,         // Released all, done
}

/// Mutex ownership state
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum MutexOwner {
    Free = 0,
    HeldByA = 1,
    HeldByB = 2,
}

/// System state for two-mutex deadlock scenario
#[derive(Debug, Clone, Copy)]
pub struct TwoMutexState {
    pub process_a: ProcessState,
    pub process_b: ProcessState,
    pub mutex1: MutexOwner,
    pub mutex2: MutexOwner,
}

impl TwoMutexState {
    /// Initial state - both processes at start, both mutexes free
    pub const fn initial() -> Self {
        TwoMutexState {
            process_a: ProcessState::Start,
            process_b: ProcessState::Start,
            mutex1: MutexOwner::Free,
            mutex2: MutexOwner::Free,
        }
    }

    /// Check if system is in deadlock state
    pub fn is_deadlock(&self) -> bool {
        // Deadlock: A holds mutex1, wants mutex2 (held by B)
        //           B holds mutex2, wants mutex1 (held by A)
        self.process_a == ProcessState::HoldFirst
            && self.process_b == ProcessState::HoldFirst
            && self.mutex1 == MutexOwner::HeldByA
            && self.mutex2 == MutexOwner::HeldByB
    }

    /// Check if system has terminated (both done)
    pub fn is_terminated(&self) -> bool {
        self.process_a == ProcessState::Done && self.process_b == ProcessState::Done
    }
}

// ============================================
// Transitions (Actions)
// ============================================

/// Try to have Process A acquire mutex1 (its first mutex)
pub fn action_a_acquire_mutex1(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_a == ProcessState::Start && state.mutex1 == MutexOwner::Free {
        Some(TwoMutexState {
            process_a: ProcessState::HoldFirst,
            mutex1: MutexOwner::HeldByA,
            ..*state
        })
    } else {
        None
    }
}

/// Try to have Process A acquire mutex2 (its second mutex)
pub fn action_a_acquire_mutex2(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_a == ProcessState::HoldFirst && state.mutex2 == MutexOwner::Free {
        Some(TwoMutexState {
            process_a: ProcessState::HoldBoth,
            mutex2: MutexOwner::HeldByA,
            ..*state
        })
    } else {
        None
    }
}

/// Process A releases both mutexes and finishes
pub fn action_a_release_and_done(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_a == ProcessState::HoldBoth {
        Some(TwoMutexState {
            process_a: ProcessState::Done,
            mutex1: MutexOwner::Free,
            mutex2: MutexOwner::Free,
            ..*state
        })
    } else {
        None
    }
}

/// Try to have Process B acquire mutex2 (its first mutex)
pub fn action_b_acquire_mutex2(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_b == ProcessState::Start && state.mutex2 == MutexOwner::Free {
        Some(TwoMutexState {
            process_b: ProcessState::HoldFirst,
            mutex2: MutexOwner::HeldByB,
            ..*state
        })
    } else {
        None
    }
}

/// Try to have Process B acquire mutex1 (its second mutex)
pub fn action_b_acquire_mutex1(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_b == ProcessState::HoldFirst && state.mutex1 == MutexOwner::Free {
        Some(TwoMutexState {
            process_b: ProcessState::HoldBoth,
            mutex1: MutexOwner::HeldByB,
            ..*state
        })
    } else {
        None
    }
}

/// Process B releases both mutexes and finishes
pub fn action_b_release_and_done(state: &TwoMutexState) -> Option<TwoMutexState> {
    if state.process_b == ProcessState::HoldBoth {
        Some(TwoMutexState {
            process_b: ProcessState::Done,
            mutex1: MutexOwner::Free,
            mutex2: MutexOwner::Free,
            ..*state
        })
    } else {
        None
    }
}

// ============================================
// State Space Exploration
// ============================================

/// All possible actions in the system
type Action = fn(&TwoMutexState) -> Option<TwoMutexState>;

const ALL_ACTIONS: [Action; 6] = [
    action_a_acquire_mutex1,
    action_a_acquire_mutex2,
    action_a_release_and_done,
    action_b_acquire_mutex2,
    action_b_acquire_mutex1,
    action_b_release_and_done,
];

const ACTION_NAMES: [&str; 6] = [
    "A_acquire_mutex1",
    "A_acquire_mutex2",
    "A_release_and_done",
    "B_acquire_mutex2",
    "B_acquire_mutex1",
    "B_release_and_done",
];

/// Encode state as u16 for efficient state space tracking
fn state_to_u16(s: &TwoMutexState) -> u16 {
    ((s.process_a as u16) << 12)
        | ((s.process_b as u16) << 8)
        | ((s.mutex1 as u16) << 4)
        | (s.mutex2 as u16)
}

/// Decode state from u16
fn u16_to_state(v: u16) -> TwoMutexState {
    // For simplicity, just decode back
    let process_a = match (v >> 12) & 0xF {
        0 => ProcessState::Start,
        1 => ProcessState::HoldFirst,
        2 => ProcessState::HoldBoth,
        _ => ProcessState::Done,
    };
    let process_b = match (v >> 8) & 0xF {
        0 => ProcessState::Start,
        1 => ProcessState::HoldFirst,
        2 => ProcessState::HoldBoth,
        _ => ProcessState::Done,
    };
    let mutex1 = match (v >> 4) & 0xF {
        0 => MutexOwner::Free,
        1 => MutexOwner::HeldByA,
        _ => MutexOwner::HeldByB,
    };
    let mutex2 = match v & 0xF {
        0 => MutexOwner::Free,
        1 => MutexOwner::HeldByA,
        _ => MutexOwner::HeldByB,
    };
    TwoMutexState {
        process_a,
        process_b,
        mutex1,
        mutex2,
    }
}

/// Explore state space and find deadlock
/// Returns (found_deadlock, deadlock_trace, states_explored)
pub fn explore_state_space() -> (bool, Vec<(String, u16)>, usize) {
    use std::collections::HashSet;

    let mut visited: HashSet<u16> = HashSet::new();
    let mut queue: Vec<(u16, Vec<(String, u16)>)> = Vec::new();
    let mut states_explored: usize = 0;

    let initial = TwoMutexState::initial();
    let initial_encoded = state_to_u16(&initial);
    visited.insert(initial_encoded);
    queue.push((initial_encoded, vec![("Initial".to_string(), initial_encoded)]));

    while let Some((state_enc, trace)) = queue.pop() {
        states_explored = states_explored.saturating_add(1);
        let state = u16_to_state(state_enc);

        // Check for deadlock
        if state.is_deadlock() {
            return (true, trace, states_explored);
        }

        // Try all actions
        for (i, action) in ALL_ACTIONS.iter().enumerate() {
            if let Some(next) = action(&state) {
                let next_enc = state_to_u16(&next);
                if !visited.contains(&next_enc) {
                    visited.insert(next_enc);
                    let mut new_trace = trace.clone();
                    let action_name = ACTION_NAMES.get(i).copied().unwrap_or("unknown");
                    new_trace.push((action_name.to_string(), next_enc));
                    queue.push((next_enc, new_trace));
                }
            }
        }
    }

    (false, vec![], states_explored)
}

// ============================================
// Property Verification
// ============================================

/// Verify: No reachable deadlock state (SHOULD FAIL)
pub fn verify_no_deadlock() -> bool {
    let (found, _trace, _explored) = explore_state_space();
    !found // Returns false if deadlock found
}

/// Find counterexample trace to deadlock
pub fn find_deadlock_trace() -> Option<Vec<(String, TwoMutexState)>> {
    let (found, trace, _explored) = explore_state_space();
    if found {
        Some(
            trace
                .into_iter()
                .map(|(action, enc)| (action, u16_to_state(enc)))
                .collect(),
        )
    } else {
        None
    }
}

// ============================================
// TLA2 Integration Format
// ============================================

/// Generate TLA2 StateMachine format from this specification
pub fn generate_tla2_statemachine() -> String {
    let mut out = String::new();
    out.push_str("// TLA2 StateMachine: TwoMutexDeadlock\n");
    out.push_str("StateMachine {\n");
    out.push_str("  name: \"TwoMutexDeadlock\",\n");
    out.push_str("  variables: [\n");
    out.push_str("    Variable { name: \"process_a\", ty: Enum { variants: [\"Start\", \"HoldFirst\", \"HoldBoth\", \"Done\"] } },\n");
    out.push_str("    Variable { name: \"process_b\", ty: Enum { variants: [\"Start\", \"HoldFirst\", \"HoldBoth\", \"Done\"] } },\n");
    out.push_str("    Variable { name: \"mutex1\", ty: Enum { variants: [\"Free\", \"HeldByA\", \"HeldByB\"] } },\n");
    out.push_str("    Variable { name: \"mutex2\", ty: Enum { variants: [\"Free\", \"HeldByA\", \"HeldByB\"] } },\n");
    out.push_str("  ],\n");
    out.push_str("  init: And([\n");
    out.push_str("    Compare(Var(\"process_a\"), Eq, Lit(\"Start\")),\n");
    out.push_str("    Compare(Var(\"process_b\"), Eq, Lit(\"Start\")),\n");
    out.push_str("    Compare(Var(\"mutex1\"), Eq, Lit(\"Free\")),\n");
    out.push_str("    Compare(Var(\"mutex2\"), Eq, Lit(\"Free\")),\n");
    out.push_str("  ]),\n");
    out.push_str("  transitions: [...], // See action functions\n");
    out.push_str("  property: Always(Not(Deadlock)), // Deadlock = both stuck\n");
    out.push_str("}\n");
    out
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== TLA2 Test Case: Two-Mutex Deadlock ===\n");

    println!("Scenario:");
    println!("  Process A: lock(mutex1) -> lock(mutex2) -> release");
    println!("  Process B: lock(mutex2) -> lock(mutex1) -> release\n");

    println!("Exploring state space...\n");

    let (found_deadlock, trace, states_explored) = explore_state_space();

    println!("States explored: {}", states_explored);
    println!("Deadlock found: {}\n", found_deadlock);

    if found_deadlock {
        println!("Counterexample trace to deadlock:");
        for (i, (action, enc)) in trace.iter().enumerate() {
            let state = u16_to_state(*enc);
            println!(
                "  Step {}: {} -> A:{:?}, B:{:?}, M1:{:?}, M2:{:?}",
                i, action, state.process_a, state.process_b, state.mutex1, state.mutex2
            );
        }
        println!();
    }

    // Verify property (should fail)
    let no_deadlock = verify_no_deadlock();
    println!(
        "Property 'No Deadlock': {} (expected: DISPROVEN)",
        if no_deadlock { "PROVEN" } else { "DISPROVEN" }
    );

    // Runtime assertions
    assert!(found_deadlock, "Expected to find deadlock");
    assert!(!no_deadlock, "Expected property to be disproven");
    assert!(states_explored > 0 && states_explored < 100, "Reasonable state space");

    println!("\n=== Test Complete: Deadlock correctly detected ===");
}

// ============================================
// Unit Tests
// ============================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let s = TwoMutexState::initial();
        assert_eq!(s.process_a, ProcessState::Start);
        assert_eq!(s.process_b, ProcessState::Start);
        assert_eq!(s.mutex1, MutexOwner::Free);
        assert_eq!(s.mutex2, MutexOwner::Free);
    }

    #[test]
    fn test_deadlock_detection() {
        let deadlock_state = TwoMutexState {
            process_a: ProcessState::HoldFirst,
            process_b: ProcessState::HoldFirst,
            mutex1: MutexOwner::HeldByA,
            mutex2: MutexOwner::HeldByB,
        };
        assert!(deadlock_state.is_deadlock());
    }

    #[test]
    fn test_finds_deadlock() {
        let (found, _, _) = explore_state_space();
        assert!(found, "Should find deadlock in two-mutex scenario");
    }

    #[test]
    fn test_state_encoding() {
        let s = TwoMutexState::initial();
        let enc = state_to_u16(&s);
        let dec = u16_to_state(enc);
        assert_eq!(s.process_a, dec.process_a);
        assert_eq!(s.process_b, dec.process_b);
        assert_eq!(s.mutex1, dec.mutex1);
        assert_eq!(s.mutex2, dec.mutex2);
    }
}
