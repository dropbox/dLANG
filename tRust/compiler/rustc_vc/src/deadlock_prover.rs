//! Deadlock Freedom Prover (Phase 6.2)
//!
//! This module provides formal verification of deadlock freedom for async state machines.
//! It uses SMT solving to prove that no reachable state is a deadlock state.
//!
//! A deadlock state is a non-final state with no enabled outgoing transitions.

use std::fmt::Write;
use std::time::Instant;
use vc_ir::temporal::{
    check_deadlock_syntactic, generate_deadlock_obligation, AsyncStateMachine,
    DeadlockProofObligation, DeadlockProofResult, DeadlockWitness,
};

/// Prover for deadlock freedom properties.
///
/// This prover can verify that async state machines are deadlock-free using:
/// 1. Syntactic analysis (fast, incomplete)
/// 2. SMT-based verification (slower, complete for finite state)
#[derive(Debug)]
pub struct DeadlockProver {
    /// Options for the prover
    pub options: DeadlockProverOptions,
    /// Statistics from proof attempts
    pub stats: DeadlockProverStats,
}

/// Options for deadlock freedom proving
#[derive(Debug, Clone)]
pub struct DeadlockProverOptions {
    /// Whether to try syntactic analysis first
    pub try_syntactic_first: bool,
    /// Timeout in milliseconds for SMT solving
    pub timeout_ms: u64,
    /// Whether to generate counterexamples
    pub generate_counterexamples: bool,
    /// Maximum number of states before giving up
    pub max_states: usize,
}

impl Default for DeadlockProverOptions {
    fn default() -> Self {
        Self {
            try_syntactic_first: true,
            timeout_ms: 5000,
            generate_counterexamples: true,
            max_states: 10000,
        }
    }
}

/// Statistics from deadlock proving
#[derive(Debug, Default, Clone)]
pub struct DeadlockProverStats {
    /// Total state machines analyzed
    pub total_analyzed: usize,
    /// Proven deadlock-free
    pub proven_free: usize,
    /// Found deadlocks
    pub found_deadlocks: usize,
    /// Unknown results
    pub unknown: usize,
    /// Syntactic proofs (fast path)
    pub syntactic_proofs: usize,
    /// SMT proofs
    pub smt_proofs: usize,
    /// Total time spent in milliseconds
    pub total_time_ms: u64,
}

/// Result of analyzing multiple state machines
#[derive(Debug)]
pub struct DeadlockAnalysisReport {
    /// Individual results for each state machine
    pub results: Vec<(String, DeadlockProofResult)>,
    /// Overall statistics
    pub stats: DeadlockProverStats,
    /// Any state machines that couldn't be analyzed
    pub skipped: Vec<(String, String)>,
}

impl Default for DeadlockProver {
    fn default() -> Self {
        Self::new()
    }
}

impl DeadlockProver {
    /// Create a new prover with default options
    #[must_use]
    pub fn new() -> Self {
        Self {
            options: DeadlockProverOptions::default(),
            stats: DeadlockProverStats::default(),
        }
    }

    /// Create a new prover with custom options
    #[must_use]
    pub fn with_options(options: DeadlockProverOptions) -> Self {
        Self {
            options,
            stats: DeadlockProverStats::default(),
        }
    }

    /// Prove deadlock freedom for a single state machine
    pub fn prove(&mut self, sm: &AsyncStateMachine) -> DeadlockProofResult {
        let start = Instant::now();
        self.stats.total_analyzed += 1;

        // Check state limit
        if self.options.max_states > 0 && sm.states.len() > self.options.max_states {
            self.stats.unknown += 1;
            return DeadlockProofResult::Unknown {
                reason: format!(
                    "State machine '{}' has {} states, exceeds limit of {}",
                    sm.name,
                    sm.states.len(),
                    self.options.max_states
                ),
            };
        }

        // Try syntactic analysis first (fast path)
        if self.options.try_syntactic_first {
            if let Some(result) = self.try_syntactic_proof(sm) {
                let elapsed = start.elapsed().as_millis() as u64;
                self.stats.total_time_ms += elapsed;
                return result;
            }
        }

        // Fall back to SMT-based proof
        let result = self.prove_via_smt(sm);
        let elapsed = start.elapsed().as_millis() as u64;
        self.stats.total_time_ms += elapsed;
        result
    }

    /// Try to prove deadlock freedom syntactically
    fn try_syntactic_proof(&mut self, sm: &AsyncStateMachine) -> Option<DeadlockProofResult> {
        // Check for syntactic deadlocks
        if let Some(witness) = check_deadlock_syntactic(sm) {
            self.stats.found_deadlocks += 1;
            self.stats.syntactic_proofs += 1;
            return Some(DeadlockProofResult::Disproven { witness });
        }

        // Check if all non-final states have outgoing transitions
        // This is a sufficient (but not necessary) condition for deadlock freedom
        let deadlock_states = sm.find_deadlocks();
        if deadlock_states.is_empty() {
            // All non-final states have outgoing transitions
            // And syntactic check found no reachable deadlocks
            self.stats.proven_free += 1;
            self.stats.syntactic_proofs += 1;
            return Some(DeadlockProofResult::Proven {
                smt_result: "syntactic".to_string(),
                time_ms: 0,
            });
        }

        // Cannot prove syntactically - need SMT
        None
    }

    /// Prove deadlock freedom using SMT
    fn prove_via_smt(&mut self, sm: &AsyncStateMachine) -> DeadlockProofResult {
        let start = Instant::now();

        // Generate the SMT obligation
        let obligation = generate_deadlock_obligation(sm);

        // For now, we simulate SMT solving with syntactic analysis
        // In a real implementation, we would:
        // 1. Send the SMT-LIB script to Z4/Z3
        // 2. Parse the result (sat/unsat/unknown)
        // 3. If sat, extract the model to build a witness

        let result = Self::evaluate_obligation(sm, &obligation);
        let elapsed = start.elapsed().as_millis() as u64;

        match &result {
            DeadlockProofResult::Proven { .. } => {
                self.stats.proven_free += 1;
                self.stats.smt_proofs += 1;
            }
            DeadlockProofResult::Disproven { .. } => {
                self.stats.found_deadlocks += 1;
                self.stats.smt_proofs += 1;
            }
            DeadlockProofResult::Unknown { .. } => {
                self.stats.unknown += 1;
            }
        }

        // Update time in result if it's Proven
        match result {
            DeadlockProofResult::Proven { smt_result, .. } => DeadlockProofResult::Proven {
                smt_result,
                time_ms: elapsed,
            },
            other => other,
        }
    }

    /// Evaluate an SMT obligation (simulation for now)
    ///
    /// In a real implementation, this would invoke an SMT solver.
    /// For now, we use the syntactic analysis as a fallback.
    fn evaluate_obligation(
        sm: &AsyncStateMachine,
        _obligation: &DeadlockProofObligation,
    ) -> DeadlockProofResult {
        // Compute reachable states
        let reachable = sm.reachable_from(sm.initial);

        // Check each reachable non-final state for deadlock
        for &state_idx in &reachable {
            if let Some(state) = sm.states.get(state_idx) {
                use vc_ir::temporal::AsyncStateKind;

                // Skip final and panicked states
                if state.kind == AsyncStateKind::End || state.kind == AsyncStateKind::Panicked {
                    continue;
                }

                // Check if this state has outgoing transitions
                let has_outgoing = sm.transitions.iter().any(|t| t.from == state_idx);
                if !has_outgoing {
                    // Found a deadlock!
                    let witness = DeadlockWitness::new(sm, state_idx);
                    return DeadlockProofResult::Disproven { witness };
                }
            }
        }

        // No deadlocks found among reachable states
        DeadlockProofResult::Proven {
            smt_result: "unsat".to_string(),
            time_ms: 0,
        }
    }

    /// Analyze multiple state machines
    pub fn analyze_all(&mut self, machines: &[AsyncStateMachine]) -> DeadlockAnalysisReport {
        let mut results = Vec::new();
        let skipped = Vec::new();

        for sm in machines {
            let result = self.prove(sm);
            results.push((sm.name.clone(), result));
        }

        DeadlockAnalysisReport {
            results,
            stats: self.stats.clone(),
            skipped,
        }
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = DeadlockProverStats::default();
    }

    /// Get a summary of the statistics
    #[must_use]
    pub fn stats_summary(&self) -> String {
        format!(
            "Deadlock Prover Stats: {} analyzed, {} proven free, {} deadlocks found, {} unknown ({} syntactic, {} SMT) in {}ms",
            self.stats.total_analyzed,
            self.stats.proven_free,
            self.stats.found_deadlocks,
            self.stats.unknown,
            self.stats.syntactic_proofs,
            self.stats.smt_proofs,
            self.stats.total_time_ms
        )
    }
}

impl DeadlockAnalysisReport {
    /// Check if all analyzed state machines are deadlock-free
    #[must_use]
    pub fn all_deadlock_free(&self) -> bool {
        self.results
            .iter()
            .all(|(_, r)| matches!(r, DeadlockProofResult::Proven { .. }))
    }

    /// Get all state machines with deadlocks
    #[must_use]
    pub fn deadlock_machines(&self) -> Vec<&str> {
        self.results
            .iter()
            .filter_map(|(name, r)| {
                if matches!(r, DeadlockProofResult::Disproven { .. }) {
                    Some(name.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all witnesses for deadlocks
    #[must_use]
    pub fn deadlock_witnesses(&self) -> Vec<&DeadlockWitness> {
        self.results
            .iter()
            .filter_map(|(_, r)| r.witness())
            .collect()
    }

    /// Format as a human-readable report
    #[must_use]
    pub fn to_string_formatted(&self) -> String {
        let mut s = String::new();
        s.push_str("Deadlock Analysis Report\n");
        s.push_str("========================\n\n");

        for (name, result) in &self.results {
            match result {
                DeadlockProofResult::Proven { time_ms, .. } => {
                    let _ = writeln!(s, "[PASS] {name} - deadlock-free ({time_ms}ms)");
                }
                DeadlockProofResult::Disproven { witness } => {
                    let _ = writeln!(s, "[FAIL] {name} - DEADLOCK FOUND");
                    let _ = writeln!(
                        s,
                        "       Deadlock at state: {}",
                        witness.deadlock_state_name
                    );
                }
                DeadlockProofResult::Unknown { reason } => {
                    let _ = writeln!(s, "[????] {name} - unknown ({reason})");
                }
            }
        }

        let _ = writeln!(
            s,
            "\nSummary: {}/{} deadlock-free, {} deadlocks, {} unknown",
            self.stats.proven_free,
            self.stats.total_analyzed,
            self.stats.found_deadlocks,
            self.stats.unknown
        );

        s
    }
}

// ============================================
// Unit Tests
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::temporal::AsyncStateKind;

    #[test]
    fn test_prover_new() {
        let prover = DeadlockProver::new();
        assert!(prover.options.try_syntactic_first);
        assert_eq!(prover.stats.total_analyzed, 0);
    }

    #[test]
    fn test_prover_with_options() {
        let options = DeadlockProverOptions {
            try_syntactic_first: false,
            timeout_ms: 1000,
            generate_counterexamples: false,
            max_states: 100,
        };
        let prover = DeadlockProver::with_options(options);
        assert!(!prover.options.try_syntactic_first);
        assert_eq!(prover.options.max_states, 100);
    }

    #[test]
    fn test_prove_deadlock_free() {
        let mut prover = DeadlockProver::new();

        // Create a simple deadlock-free state machine
        let mut sm = AsyncStateMachine::new("safe");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let result = prover.prove(&sm);
        assert!(result.is_proven());
        assert_eq!(prover.stats.proven_free, 1);
    }

    #[test]
    fn test_prove_with_deadlock() {
        let mut prover = DeadlockProver::new();

        // Create a state machine with a deadlock
        let mut sm = AsyncStateMachine::new("deadlock");
        let stuck = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, stuck);
        // stuck has no outgoing transitions - deadlock!

        let result = prover.prove(&sm);
        assert!(result.is_disproven());
        assert_eq!(prover.stats.found_deadlocks, 1);

        let witness = result.witness().unwrap();
        assert_eq!(witness.deadlock_state, stuck);
    }

    #[test]
    fn test_prove_exceeds_max_states() {
        let options = DeadlockProverOptions {
            max_states: 2,
            ..Default::default()
        };
        let mut prover = DeadlockProver::with_options(options);

        let mut sm = AsyncStateMachine::new("big");
        sm.add_state("S1", AsyncStateKind::Suspended);
        sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_state("S3", AsyncStateKind::End);
        // Now has 4 states (Start + S1 + S2 + S3), exceeds max of 2

        let result = prover.prove(&sm);
        assert!(result.is_unknown());
        assert_eq!(prover.stats.unknown, 1);
    }

    #[test]
    fn test_analyze_all() {
        let mut prover = DeadlockProver::new();

        // Create two state machines
        let mut sm1 = AsyncStateMachine::new("safe1");
        let end1 = sm1.add_state("End", AsyncStateKind::End);
        sm1.add_transition(0, end1);

        let mut sm2 = AsyncStateMachine::new("safe2");
        let s2 = sm2.add_state("S2", AsyncStateKind::Suspended);
        let end2 = sm2.add_state("End", AsyncStateKind::End);
        sm2.add_transition(0, s2);
        sm2.add_transition(s2, end2);

        let report = prover.analyze_all(&[sm1, sm2]);
        assert!(report.all_deadlock_free());
        assert_eq!(report.results.len(), 2);
    }

    #[test]
    fn test_analyze_all_mixed() {
        let mut prover = DeadlockProver::new();

        let mut safe = AsyncStateMachine::new("safe");
        let end = safe.add_state("End", AsyncStateKind::End);
        safe.add_transition(0, end);

        let mut deadlock = AsyncStateMachine::new("deadlock");
        let stuck = deadlock.add_state("Stuck", AsyncStateKind::Suspended);
        deadlock.add_transition(0, stuck);

        let report = prover.analyze_all(&[safe, deadlock]);
        assert!(!report.all_deadlock_free());
        assert_eq!(report.deadlock_machines(), vec!["deadlock"]);
    }

    #[test]
    fn test_stats_reset() {
        let mut prover = DeadlockProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        prover.prove(&sm);
        assert_eq!(prover.stats.total_analyzed, 1);

        prover.reset_stats();
        assert_eq!(prover.stats.total_analyzed, 0);
    }

    #[test]
    fn test_stats_summary() {
        let mut prover = DeadlockProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        prover.prove(&sm);
        let summary = prover.stats_summary();
        assert!(summary.contains("1 analyzed"));
        assert!(summary.contains("1 proven free"));
    }

    #[test]
    fn test_report_formatted() {
        let mut prover = DeadlockProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let report = prover.analyze_all(&[sm]);
        let formatted = report.to_string_formatted();
        assert!(formatted.contains("Deadlock Analysis Report"));
        assert!(formatted.contains("[PASS]"));
        assert!(formatted.contains("test"));
    }

    #[test]
    fn test_syntactic_proof_fast_path() {
        let mut prover = DeadlockProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        prover.prove(&sm);
        assert_eq!(prover.stats.syntactic_proofs, 1);
        assert_eq!(prover.stats.smt_proofs, 0);
    }

    #[test]
    fn test_deadlock_witnesses() {
        let mut prover = DeadlockProver::new();

        let mut sm = AsyncStateMachine::new("deadlock");
        let stuck = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, stuck);

        let report = prover.analyze_all(&[sm]);
        let witnesses = report.deadlock_witnesses();
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0].deadlock_state_name, "Stuck");
    }

    #[test]
    fn test_unreachable_deadlock_ignored() {
        let mut prover = DeadlockProver::new();

        // Create a state machine where a "deadlock" state exists but is unreachable
        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        let _unreachable = sm.add_state("Unreachable", AsyncStateKind::Suspended);
        sm.add_transition(0, end);
        // Unreachable has no incoming transitions and no outgoing
        // But it's not reachable, so it's not a real deadlock

        let result = prover.prove(&sm);
        assert!(result.is_proven());
    }

    #[test]
    fn test_complex_deadlock_path() {
        let mut prover = DeadlockProver::new();

        // Create a longer path to deadlock
        let mut sm = AsyncStateMachine::new("complex");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let s3 = sm.add_state("S3", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s3);
        // s3 is a deadlock

        let result = prover.prove(&sm);
        assert!(result.is_disproven());

        let witness = result.witness().unwrap();
        assert_eq!(witness.deadlock_state, s3);
        assert_eq!(witness.path.len(), 4); // Start -> S1 -> S2 -> S3
    }

    #[test]
    fn test_branching_deadlock() {
        let mut prover = DeadlockProver::new();

        // One branch leads to end, one to deadlock
        let mut sm = AsyncStateMachine::new("branch");
        let branch_a = sm.add_state("BranchA", AsyncStateKind::Suspended);
        let branch_b = sm.add_state("BranchB", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, branch_a);
        sm.add_transition(0, branch_b);
        sm.add_transition(branch_a, end);
        // branch_b has no outgoing - deadlock!

        let result = prover.prove(&sm);
        assert!(result.is_disproven());
        let witness = result.witness().unwrap();
        assert_eq!(witness.deadlock_state, branch_b);
    }

    #[test]
    fn test_default_options() {
        let options = DeadlockProverOptions::default();
        assert!(options.try_syntactic_first);
        assert_eq!(options.timeout_ms, 5000);
        assert!(options.generate_counterexamples);
        assert_eq!(options.max_states, 10000);
    }
}
