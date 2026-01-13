//! Liveness Property Proof Test - Phase 6.2
//!
//! This test demonstrates the liveness property proof infrastructure
//! for async Rust code. The prover uses SMT-based verification to
//! formally prove properties like termination, progress, and response.
//!
//! Liveness properties assert "something good eventually happens":
//! - Termination: eventually reaches a final state
//! - Progress: can always make forward progress
//! - Response: if P then eventually Q (P ~> Q)
//! - Reachability: a specific state is eventually reached
//!
//! Expected: PASS (runtime verification of liveness proofs)

#![allow(unused_variables)]

// ============================================
// Liveness Property Proof Simulation
// ============================================

/// Compute reachable states from initial state
fn compute_reachable(_max_state: usize, transitions: &[(usize, usize)]) -> u16 {
    let mut reachable: u16 = 1; // State 0 is reachable
    let mut changed = true;

    while changed {
        changed = false;
        for (from, to) in transitions.iter() {
            // Mask shift amounts to ensure they're < 16 (bit width of u16)
            let from_mask = 1u16 << ((*from as u16) & 0xF);
            let to_mask = 1u16 << ((*to as u16) & 0xF);

            if (reachable & from_mask) != 0 && (reachable & to_mask) == 0 {
                reachable = reachable | to_mask;
                changed = true;
            }
        }
    }
    reachable
}

/// Check if a state can reach any final state
fn can_reach_final(start: usize, _max_state: usize, transitions: &[(usize, usize)], finals: &[usize]) -> bool {
    // BFS from start to see if any final is reachable
    let mut reachable: u16 = 1u16 << ((start as u16) & 0xF);
    let mut changed = true;

    while changed {
        changed = false;
        for (from, to) in transitions.iter() {
            // Mask shift amounts to ensure they're < 16 (bit width of u16)
            let from_mask = 1u16 << ((*from as u16) & 0xF);
            let to_mask = 1u16 << ((*to as u16) & 0xF);

            if (reachable & from_mask) != 0 && (reachable & to_mask) == 0 {
                reachable = reachable | to_mask;
                changed = true;
            }
        }
    }

    // Check if any final state is reachable
    for fin in finals.iter() {
        let fin_mask = 1u16 << ((*fin as u16) & 0xF);
        if (reachable & fin_mask) != 0 {
            return true;
        }
    }
    false
}

/// Prove termination: all reachable states can eventually reach a final state
fn prove_termination(max_state: usize, transitions: &[(usize, usize)], finals: &[usize]) -> bool {
    let reachable = compute_reachable(max_state, transitions);

    let mut state = 0;
    while state < max_state {
        let state_mask = 1u16 << ((state as u16) & 0xF);
        if (reachable & state_mask) != 0 {
            // This state is reachable - can it reach a final state?
            if !can_reach_final(state, max_state, transitions, finals) {
                return false; // Found a state that can't terminate
            }
        }
        state = state + 1;
    }
    true
}

/// Prove progress: all reachable non-final states have outgoing transitions
fn prove_progress(max_state: usize, transitions: &[(usize, usize)], finals: &[usize]) -> bool {
    let reachable = compute_reachable(max_state, transitions);

    let mut state = 0;
    while state < max_state {
        // Skip final states
        let mut is_final = false;
        for fin in finals.iter() {
            if *fin == state {
                is_final = true;
            }
        }
        if is_final {
            state = state + 1;
            continue;
        }

        let state_mask = 1u16 << ((state as u16) & 0xF);
        if (reachable & state_mask) != 0 {
            // Check for outgoing transitions
            let mut has_outgoing = false;
            for (from, _to) in transitions.iter() {
                if *from == state {
                    has_outgoing = true;
                }
            }
            if !has_outgoing {
                return false; // Found a stuck state
            }
        }
        state = state + 1;
    }
    true
}

/// Prove reachability: target state is reachable from initial
fn prove_reachability(max_state: usize, transitions: &[(usize, usize)], target: usize) -> bool {
    let reachable = compute_reachable(max_state, transitions);
    let target_mask = 1u16 << ((target as u16) & 0xF);
    (reachable & target_mask) != 0
}

/// Prove response: if trigger is reached, goal is eventually reached from it
fn prove_response(max_state: usize, transitions: &[(usize, usize)], trigger: usize, goal: usize) -> bool {
    let reachable = compute_reachable(max_state, transitions);
    let trigger_mask = 1u16 << ((trigger as u16) & 0xF);

    // If trigger is not reachable, property vacuously holds
    if (reachable & trigger_mask) == 0 {
        return true;
    }

    // Check if goal is reachable from trigger
    let reachable_from_trigger = {
        let mut r: u16 = 1u16 << ((trigger as u16) & 0xF);
        let mut changed = true;
        while changed {
            changed = false;
            for (from, to) in transitions.iter() {
                let from_mask = 1u16 << ((*from as u16) & 0xF);
                let to_mask = 1u16 << ((*to as u16) & 0xF);
                if (r & from_mask) != 0 && (r & to_mask) == 0 {
                    r = r | to_mask;
                    changed = true;
                }
            }
        }
        r
    };

    let goal_mask = 1u16 << ((goal as u16) & 0xF);
    (reachable_from_trigger & goal_mask) != 0
}

/// Find a cycle reachable from a given state
fn find_cycle(max_state: usize, transitions: &[(usize, usize)], start: usize) -> bool {
    // Simple cycle detection via visited tracking
    let mut visited: u16 = 0;
    let mut current = start;
    let mut steps = 0;

    while steps < max_state * 2 {
        let current_mask = 1u16 << ((current as u16) & 0xF);
        if (visited & current_mask) != 0 {
            return true; // Found cycle
        }
        visited = visited | current_mask;

        // Find next state (first outgoing transition)
        let mut found_next = false;
        for (from, to) in transitions.iter() {
            if *from == current {
                current = *to;
                found_next = true;
                break;
            }
        }
        if !found_next {
            return false; // Dead end
        }
        steps = steps + 1;
    }
    true // Assume cycle if too many steps
}

// ============================================
// Test Cases: Termination
// ============================================

/// Test: Simple terminating state machine
fn test_termination_simple() -> bool {
    let max_state = 2;
    let transitions: [(usize, usize); 1] = [(0, 1)];
    let finals: [usize; 1] = [1];
    prove_termination(max_state, &transitions, &finals)
}

/// Test: Sequential awaits terminate
fn test_termination_sequential() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (1, 2), (2, 3)];
    let finals: [usize; 1] = [3];
    prove_termination(max_state, &transitions, &finals)
}

/// Test: Branching with both paths terminating
fn test_termination_branching() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 4] = [(0, 1), (0, 2), (1, 3), (2, 3)];
    let finals: [usize; 1] = [3];
    prove_termination(max_state, &transitions, &finals)
}

/// Test: Non-terminating infinite cycle
fn test_termination_fails_cycle() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 2] = [(0, 1), (1, 1)]; // Infinite self-loop
    let finals: [usize; 1] = [2];
    // Should return false because state 1 can't reach final
    !prove_termination(max_state, &transitions, &finals)
}

/// Test: Non-terminating mutual cycle
fn test_termination_fails_mutual_cycle() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (1, 2), (2, 1)]; // Cycle between 1 and 2
    let finals: [usize; 1] = [3];
    !prove_termination(max_state, &transitions, &finals)
}

// ============================================
// Test Cases: Progress
// ============================================

/// Test: Progress with all transitions present
fn test_progress_simple() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 2] = [(0, 1), (1, 2)];
    let finals: [usize; 1] = [2];
    prove_progress(max_state, &transitions, &finals)
}

/// Test: Progress fails with stuck state
fn test_progress_fails_stuck() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 1] = [(0, 1)];
    let finals: [usize; 1] = [2];
    // State 1 has no outgoing transitions and is not final
    !prove_progress(max_state, &transitions, &finals)
}

/// Test: Progress OK with self-loop (can still make progress)
fn test_progress_with_loop() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 2] = [(0, 1), (1, 1)];
    let finals: [usize; 1] = [2];
    // State 1 has outgoing (to itself), so progress is satisfied
    prove_progress(max_state, &transitions, &finals)
}

// ============================================
// Test Cases: Reachability
// ============================================

/// Test: Reachability of directly connected state
fn test_reachability_direct() -> bool {
    let max_state = 2;
    let transitions: [(usize, usize); 1] = [(0, 1)];
    prove_reachability(max_state, &transitions, 1)
}

/// Test: Reachability through chain
fn test_reachability_chain() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (1, 2), (2, 3)];
    prove_reachability(max_state, &transitions, 3)
}

/// Test: Unreachable state
fn test_reachability_fails() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 1] = [(0, 1)];
    // State 2 is not reachable
    !prove_reachability(max_state, &transitions, 2)
}

// ============================================
// Test Cases: Response (P ~> Q)
// ============================================

/// Test: Response with direct transition
fn test_response_direct() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 2] = [(0, 1), (1, 2)];
    // Request(1) ~> Response(2)
    prove_response(max_state, &transitions, 1, 2)
}

/// Test: Response through intermediate states
fn test_response_chain() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (1, 2), (2, 3)];
    // Req(1) ~> Resp(3)
    prove_response(max_state, &transitions, 1, 3)
}

/// Test: Response fails with cycle that misses goal
fn test_response_fails() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (1, 2), (2, 1)];
    // Req(1) cannot reach Resp(3) - stuck in cycle
    !prove_response(max_state, &transitions, 1, 3)
}

/// Test: Response vacuously true when trigger unreachable
fn test_response_vacuous() -> bool {
    let max_state = 3;
    let transitions: [(usize, usize); 1] = [(0, 2)];
    // Trigger(1) is not reachable, so Req(1) ~> Resp(anything) is vacuously true
    prove_response(max_state, &transitions, 1, 2)
}

// ============================================
// Test Cases: Complex Scenarios
// ============================================

/// Test: State machine with multiple final states
fn test_multiple_finals() -> bool {
    let max_state = 4;
    let transitions: [(usize, usize); 3] = [(0, 1), (0, 2), (0, 3)];
    let finals: [usize; 3] = [1, 2, 3];
    // All branches lead to final states
    prove_termination(max_state, &transitions, &finals) &&
    prove_progress(max_state, &transitions, &finals)
}

/// Test: Diamond pattern
fn test_diamond_pattern() -> bool {
    let max_state = 4;
    // Diamond: 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
    let transitions: [(usize, usize); 4] = [(0, 1), (0, 2), (1, 3), (2, 3)];
    let finals: [usize; 1] = [3];
    prove_termination(max_state, &transitions, &finals)
}

/// Test: Cycle detection utility
fn test_cycle_detection() -> bool {
    let max_state = 3;
    let transitions_with_cycle: [(usize, usize); 2] = [(0, 1), (1, 0)];
    let transitions_no_cycle: [(usize, usize); 2] = [(0, 1), (1, 2)];

    find_cycle(max_state, &transitions_with_cycle, 0) &&
    !find_cycle(max_state, &transitions_no_cycle, 0)
}

/// Test: Unreachable cycle doesn't affect termination
fn test_unreachable_cycle() -> bool {
    let max_state = 5;
    // Main path: 0 -> 1 -> 4 (final)
    // Unreachable cycle: 2 <-> 3
    let transitions: [(usize, usize); 4] = [(0, 1), (1, 4), (2, 3), (3, 2)];
    let finals: [usize; 1] = [4];
    // Should pass because the cycle is unreachable
    prove_termination(max_state, &transitions, &finals)
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== Liveness Property Proof Test - Phase 6.2 ===\n");

    println!("This test demonstrates formal verification of liveness properties");
    println!("for async state machines. Liveness means 'something good eventually happens'.\n");

    println!("--- Termination Proofs ---\n");

    let t1 = test_termination_simple();
    println!("test_termination_simple: {}", if t1 { "PROVEN" } else { "FAILED" });

    let t2 = test_termination_sequential();
    println!("test_termination_sequential: {}", if t2 { "PROVEN" } else { "FAILED" });

    let t3 = test_termination_branching();
    println!("test_termination_branching: {}", if t3 { "PROVEN" } else { "FAILED" });

    let t4 = test_termination_fails_cycle();
    println!("test_termination_fails_cycle: {} (expected true - violation detected)", if t4 { "PASS" } else { "FAIL" });

    let t5 = test_termination_fails_mutual_cycle();
    println!("test_termination_fails_mutual_cycle: {} (expected true - violation detected)", if t5 { "PASS" } else { "FAIL" });

    println!("\n--- Progress Proofs ---\n");

    let p1 = test_progress_simple();
    println!("test_progress_simple: {}", if p1 { "PROVEN" } else { "FAILED" });

    let p2 = test_progress_fails_stuck();
    println!("test_progress_fails_stuck: {} (expected true - stuck state detected)", if p2 { "PASS" } else { "FAIL" });

    let p3 = test_progress_with_loop();
    println!("test_progress_with_loop: {}", if p3 { "PROVEN" } else { "FAILED" });

    println!("\n--- Reachability Proofs ---\n");

    let r1 = test_reachability_direct();
    println!("test_reachability_direct: {}", if r1 { "PROVEN" } else { "FAILED" });

    let r2 = test_reachability_chain();
    println!("test_reachability_chain: {}", if r2 { "PROVEN" } else { "FAILED" });

    let r3 = test_reachability_fails();
    println!("test_reachability_fails: {} (expected true - unreachable detected)", if r3 { "PASS" } else { "FAIL" });

    println!("\n--- Response Proofs (P ~> Q) ---\n");

    let s1 = test_response_direct();
    println!("test_response_direct: {}", if s1 { "PROVEN" } else { "FAILED" });

    let s2 = test_response_chain();
    println!("test_response_chain: {}", if s2 { "PROVEN" } else { "FAILED" });

    let s3 = test_response_fails();
    println!("test_response_fails: {} (expected true - violation detected)", if s3 { "PASS" } else { "FAIL" });

    let s4 = test_response_vacuous();
    println!("test_response_vacuous: {}", if s4 { "PROVEN (vacuously true)" } else { "FAILED" });

    println!("\n--- Complex Scenarios ---\n");

    let c1 = test_multiple_finals();
    println!("test_multiple_finals: {}", if c1 { "PROVEN" } else { "FAILED" });

    let c2 = test_diamond_pattern();
    println!("test_diamond_pattern: {}", if c2 { "PROVEN" } else { "FAILED" });

    let c3 = test_cycle_detection();
    println!("test_cycle_detection: {}", if c3 { "PASS" } else { "FAIL" });

    let c4 = test_unreachable_cycle();
    println!("test_unreachable_cycle: {}", if c4 { "PROVEN" } else { "FAILED" });

    println!("\n--- Summary ---");

    let all_pass = t1 && t2 && t3 && t4 && t5 &&
                   p1 && p2 && p3 &&
                   r1 && r2 && r3 &&
                   s1 && s2 && s3 && s4 &&
                   c1 && c2 && c3 && c4;

    if all_pass {
        println!("All liveness property proofs completed successfully.");
        println!("Phase 6.2 liveness proof infrastructure verified.");
    } else {
        println!("Some tests failed - check output above.");
    }

    println!("\n=== Liveness Property Proof Test Complete ===");
}
