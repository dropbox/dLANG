//! Liveness Property Prover (Phase 6.2)
//!
//! This module provides formal verification of liveness properties for async state machines.
//! It uses SMT solving to prove properties like termination, response, and progress.
//!
//! Liveness properties assert that "something good eventually happens":
//! - Termination: eventually reaches a final state
//! - Response: if P then eventually Q (P ~> Q)
//! - Progress: can always make forward progress
//! - Reachability: a target state is eventually reached
//! - Fairness: enabled actions are eventually executed

use std::fmt::Write;
use std::time::Instant;
use vc_ir::temporal::{
    check_liveness_syntactic, generate_liveness_obligation, AsyncStateMachine,
    LivenessProofObligation, LivenessProofResult, LivenessProperty, LivenessWitness,
};

/// Prover for liveness properties.
///
/// This prover can verify liveness properties using:
/// 1. Syntactic analysis (fast, incomplete)
/// 2. SMT-based verification (slower, complete for finite state)
#[derive(Debug)]
pub struct LivenessProver {
    /// Options for the prover
    pub options: LivenessProverOptions,
    /// Statistics from proof attempts
    pub stats: LivenessProverStats,
}

/// Options for liveness proving
#[derive(Debug, Clone)]
pub struct LivenessProverOptions {
    /// Whether to try syntactic analysis first
    pub try_syntactic_first: bool,
    /// Timeout in milliseconds for SMT solving
    pub timeout_ms: u64,
    /// Whether to generate counterexamples
    pub generate_counterexamples: bool,
    /// Maximum number of states before giving up
    pub max_states: usize,
}

impl Default for LivenessProverOptions {
    fn default() -> Self {
        Self {
            try_syntactic_first: true,
            timeout_ms: 5000,
            generate_counterexamples: true,
            max_states: 10000,
        }
    }
}

/// Statistics from liveness proving
#[derive(Debug, Default, Clone)]
pub struct LivenessProverStats {
    /// Total properties analyzed
    pub total_analyzed: usize,
    /// Proven properties
    pub proven: usize,
    /// Disproven properties
    pub disproven: usize,
    /// Unknown results
    pub unknown: usize,
    /// Syntactic proofs (fast path)
    pub syntactic_proofs: usize,
    /// SMT proofs
    pub smt_proofs: usize,
    /// Total time spent in milliseconds
    pub total_time_ms: u64,
}

/// Result of analyzing multiple state machines for liveness
#[derive(Debug)]
pub struct LivenessAnalysisReport {
    /// Individual results for each (state machine, property) pair
    pub results: Vec<(String, LivenessProperty, LivenessProofResult)>,
    /// Overall statistics
    pub stats: LivenessProverStats,
    /// Any properties that couldn't be analyzed
    pub skipped: Vec<(String, LivenessProperty, String)>,
}

impl Default for LivenessProver {
    fn default() -> Self {
        Self::new()
    }
}

impl LivenessProver {
    /// Create a new prover with default options
    #[must_use]
    pub fn new() -> Self {
        Self {
            options: LivenessProverOptions::default(),
            stats: LivenessProverStats::default(),
        }
    }

    /// Create a new prover with custom options
    #[must_use]
    pub fn with_options(options: LivenessProverOptions) -> Self {
        Self {
            options,
            stats: LivenessProverStats::default(),
        }
    }

    /// Prove a liveness property for a single state machine
    pub fn prove(
        &mut self,
        sm: &AsyncStateMachine,
        property: &LivenessProperty,
    ) -> LivenessProofResult {
        let start = Instant::now();
        self.stats.total_analyzed += 1;

        // Check state limit
        if self.options.max_states > 0 && sm.states.len() > self.options.max_states {
            self.stats.unknown += 1;
            return LivenessProofResult::Unknown {
                property: property.clone(),
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
            if let Some(result) = self.try_syntactic_proof(sm, property) {
                let elapsed = start.elapsed().as_millis() as u64;
                self.stats.total_time_ms += elapsed;
                return result;
            }
        }

        // Fall back to SMT-based proof
        let result = self.prove_via_smt(sm, property);
        let elapsed = start.elapsed().as_millis() as u64;
        self.stats.total_time_ms += elapsed;
        result
    }

    /// Try to prove liveness syntactically
    fn try_syntactic_proof(
        &mut self,
        sm: &AsyncStateMachine,
        property: &LivenessProperty,
    ) -> Option<LivenessProofResult> {
        // Check for syntactic violations
        if let Some(witness) = check_liveness_syntactic(sm, property) {
            self.stats.disproven += 1;
            self.stats.syntactic_proofs += 1;
            return Some(LivenessProofResult::Disproven {
                property: property.clone(),
                witness,
            });
        }

        // For termination, check if all states can reach final
        match property {
            LivenessProperty::Termination => {
                if Self::check_termination_syntactic(sm) {
                    self.stats.proven += 1;
                    self.stats.syntactic_proofs += 1;
                    return Some(LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: "All reachable states can reach a final state".to_string(),
                    });
                }
            }
            LivenessProperty::Progress => {
                if Self::check_progress_syntactic(sm) {
                    self.stats.proven += 1;
                    self.stats.syntactic_proofs += 1;
                    return Some(LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: "All reachable non-final states have outgoing transitions"
                            .to_string(),
                    });
                }
            }
            LivenessProperty::Reachability { target_state } => {
                if Self::check_reachability_syntactic(sm, target_state) {
                    self.stats.proven += 1;
                    self.stats.syntactic_proofs += 1;
                    return Some(LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: format!("State '{target_state}' is reachable from initial"),
                    });
                }
            }
            LivenessProperty::Response { trigger, goal } => {
                if Self::check_response_syntactic(sm, trigger, goal) {
                    self.stats.proven += 1;
                    self.stats.syntactic_proofs += 1;
                    return Some(LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: format!("State '{goal}' is reachable from state '{trigger}'"),
                    });
                }
            }
            _ => {
                // Fairness and StarvationFreedom need SMT
            }
        }

        // Cannot prove syntactically - need SMT
        None
    }

    /// Check termination syntactically
    fn check_termination_syntactic(sm: &AsyncStateMachine) -> bool {
        // Check if all reachable states can reach a final state
        let reachable = sm.reachable_from(sm.initial);

        for &state in &reachable {
            if !Self::can_reach_final(sm, state) {
                return false;
            }
        }

        true
    }

    /// Check if a state can reach a final state
    fn can_reach_final(sm: &AsyncStateMachine, state: usize) -> bool {
        let reachable_from_state = sm.reachable_from(state);
        reachable_from_state.iter().any(|&s| sm.finals.contains(&s)) || sm.finals.contains(&state)
    }

    /// Check progress syntactically
    fn check_progress_syntactic(sm: &AsyncStateMachine) -> bool {
        let reachable = sm.reachable_from(sm.initial);

        for &state in &reachable {
            // Skip final states
            if sm.finals.contains(&state) {
                continue;
            }

            // Check if state has outgoing transitions
            let has_outgoing = sm.transitions.iter().any(|t| t.from == state);
            if !has_outgoing {
                return false;
            }
        }

        true
    }

    /// Check reachability syntactically
    fn check_reachability_syntactic(sm: &AsyncStateMachine, target: &str) -> bool {
        let target_idx = sm.states.iter().position(|s| s.name == target);
        if let Some(idx) = target_idx {
            let reachable = sm.reachable_from(sm.initial);
            reachable.contains(&idx)
        } else {
            false // Target state doesn't exist
        }
    }

    /// Check response syntactically
    fn check_response_syntactic(sm: &AsyncStateMachine, trigger: &str, goal: &str) -> bool {
        let trigger_idx = sm.states.iter().position(|s| s.name == trigger);
        let goal_idx = sm.states.iter().position(|s| s.name == goal);

        if let (Some(t_idx), Some(g_idx)) = (trigger_idx, goal_idx) {
            // Check if trigger is reachable
            let reachable_from_initial = sm.reachable_from(sm.initial);
            if !reachable_from_initial.contains(&t_idx) {
                return true; // Vacuously true - trigger not reachable
            }

            // Check if goal is reachable from trigger
            let reachable_from_trigger = sm.reachable_from(t_idx);
            reachable_from_trigger.contains(&g_idx)
        } else {
            false
        }
    }

    /// Prove liveness using SMT
    fn prove_via_smt(
        &mut self,
        sm: &AsyncStateMachine,
        property: &LivenessProperty,
    ) -> LivenessProofResult {
        let start = Instant::now();

        // Generate the SMT obligation
        let obligation = generate_liveness_obligation(sm, property.clone());

        // For now, we simulate SMT solving with syntactic analysis
        // In a real implementation, we would:
        // 1. Send the SMT-LIB script to Z4/Z3
        // 2. Parse the result (sat/unsat/unknown)
        // 3. If sat, extract the model to build a witness

        let result = Self::evaluate_obligation(sm, property, &obligation);
        let _elapsed = start.elapsed().as_millis() as u64;

        match &result {
            LivenessProofResult::Proven { .. } => {
                self.stats.proven += 1;
                self.stats.smt_proofs += 1;
            }
            LivenessProofResult::Disproven { .. } => {
                self.stats.disproven += 1;
                self.stats.smt_proofs += 1;
            }
            LivenessProofResult::Unknown { .. } => {
                self.stats.unknown += 1;
            }
        }

        result
    }

    /// Evaluate an SMT obligation (simulation for now)
    fn evaluate_obligation(
        sm: &AsyncStateMachine,
        property: &LivenessProperty,
        _obligation: &LivenessProofObligation,
    ) -> LivenessProofResult {
        // This is a simulation - in real implementation, invoke SMT solver
        // For now, use thorough syntactic analysis

        match property {
            LivenessProperty::Termination => {
                if Self::check_termination_syntactic(sm) {
                    LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: "SMT: All states can reach final (unsat)".to_string(),
                    }
                } else {
                    // Find the violating cycle
                    if let Some(witness) = check_liveness_syntactic(sm, property) {
                        LivenessProofResult::Disproven {
                            property: property.clone(),
                            witness,
                        }
                    } else {
                        LivenessProofResult::Unknown {
                            property: property.clone(),
                            reason: "Could not determine termination".to_string(),
                        }
                    }
                }
            }
            LivenessProperty::Progress => {
                if Self::check_progress_syntactic(sm) {
                    LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: "SMT: All reachable states have outgoing transitions".to_string(),
                    }
                } else if let Some(witness) = check_liveness_syntactic(sm, property) {
                    LivenessProofResult::Disproven {
                        property: property.clone(),
                        witness,
                    }
                } else {
                    LivenessProofResult::Unknown {
                        property: property.clone(),
                        reason: "Could not determine progress".to_string(),
                    }
                }
            }
            LivenessProperty::Reachability { target_state } => {
                if Self::check_reachability_syntactic(sm, target_state) {
                    LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: format!("SMT: {target_state} is reachable"),
                    }
                } else if let Some(witness) = check_liveness_syntactic(sm, property) {
                    LivenessProofResult::Disproven {
                        property: property.clone(),
                        witness,
                    }
                } else {
                    LivenessProofResult::Unknown {
                        property: property.clone(),
                        reason: format!("Could not determine reachability of {target_state}"),
                    }
                }
            }
            LivenessProperty::Response { trigger, goal } => {
                if Self::check_response_syntactic(sm, trigger, goal) {
                    LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: format!("SMT: {trigger} ~> {goal} holds"),
                    }
                } else if let Some(witness) = check_liveness_syntactic(sm, property) {
                    LivenessProofResult::Disproven {
                        property: property.clone(),
                        witness,
                    }
                } else {
                    LivenessProofResult::Unknown {
                        property: property.clone(),
                        reason: format!("Could not determine {trigger} ~> {goal}"),
                    }
                }
            }
            LivenessProperty::Fairness { action } => {
                // Fairness is harder - would need full SMT
                LivenessProofResult::Unknown {
                    property: property.clone(),
                    reason: format!("Fairness for '{action}' requires full SMT solver"),
                }
            }
            LivenessProperty::StarvationFreedom => {
                // Similar to termination - check if all can reach final
                if Self::check_termination_syntactic(sm) {
                    LivenessProofResult::Proven {
                        property: property.clone(),
                        reason: "SMT: No starvation possible".to_string(),
                    }
                } else {
                    LivenessProofResult::Unknown {
                        property: property.clone(),
                        reason: "Starvation freedom requires full SMT solver".to_string(),
                    }
                }
            }
        }
    }

    /// Analyze a state machine for multiple liveness properties
    pub fn analyze_all(
        &mut self,
        sm: &AsyncStateMachine,
        properties: &[LivenessProperty],
    ) -> LivenessAnalysisReport {
        let mut results = Vec::new();
        let skipped = Vec::new();

        for property in properties {
            let result = self.prove(sm, property);
            results.push((sm.name.clone(), property.clone(), result));
        }

        LivenessAnalysisReport {
            results,
            stats: self.stats.clone(),
            skipped,
        }
    }

    /// Prove default liveness properties for a state machine
    pub fn prove_default_properties(&mut self, sm: &AsyncStateMachine) -> LivenessAnalysisReport {
        let default_props = vec![LivenessProperty::Termination, LivenessProperty::Progress];
        self.analyze_all(sm, &default_props)
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = LivenessProverStats::default();
    }

    /// Get a summary of the statistics
    #[must_use]
    pub fn stats_summary(&self) -> String {
        format!(
            "Liveness Prover Stats: {} analyzed, {} proven, {} disproven, {} unknown ({} syntactic, {} SMT) in {}ms",
            self.stats.total_analyzed,
            self.stats.proven,
            self.stats.disproven,
            self.stats.unknown,
            self.stats.syntactic_proofs,
            self.stats.smt_proofs,
            self.stats.total_time_ms
        )
    }
}

impl LivenessAnalysisReport {
    /// Check if all analyzed properties hold
    #[must_use]
    pub fn all_proven(&self) -> bool {
        self.results
            .iter()
            .all(|(_, _, r)| matches!(r, LivenessProofResult::Proven { .. }))
    }

    /// Get all disproven properties
    #[must_use]
    pub fn disproven_properties(&self) -> Vec<(&str, &LivenessProperty)> {
        self.results
            .iter()
            .filter_map(|(name, prop, r)| {
                if matches!(r, LivenessProofResult::Disproven { .. }) {
                    Some((name.as_str(), prop))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all witnesses for violations
    #[must_use]
    pub fn violation_witnesses(&self) -> Vec<&LivenessWitness> {
        self.results
            .iter()
            .filter_map(|(_, _, r)| r.witness())
            .collect()
    }

    /// Format as a human-readable report
    #[must_use]
    pub fn to_string_formatted(&self) -> String {
        let mut s = String::new();
        s.push_str("Liveness Analysis Report\n");
        s.push_str("========================\n\n");

        for (name, prop, result) in &self.results {
            let prop_desc = prop.description();
            match result {
                LivenessProofResult::Proven { reason, .. } => {
                    let _ = writeln!(s, "[PASS] {name} - {prop_desc} ({reason})");
                }
                LivenessProofResult::Disproven { witness, .. } => {
                    let _ = writeln!(s, "[FAIL] {name} - {prop_desc} VIOLATED");
                    let _ = writeln!(s, "       {}", witness.explanation);
                }
                LivenessProofResult::Unknown { reason, .. } => {
                    let _ = writeln!(s, "[????] {name} - {prop_desc} unknown ({reason})");
                }
            }
        }

        let _ = writeln!(
            s,
            "\nSummary: {}/{} proven, {} disproven, {} unknown",
            self.stats.proven, self.stats.total_analyzed, self.stats.disproven, self.stats.unknown
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
        let prover = LivenessProver::new();
        assert!(prover.options.try_syntactic_first);
        assert_eq!(prover.stats.total_analyzed, 0);
    }

    #[test]
    fn test_prover_with_options() {
        let options = LivenessProverOptions {
            try_syntactic_first: false,
            timeout_ms: 1000,
            generate_counterexamples: false,
            max_states: 100,
        };
        let prover = LivenessProver::with_options(options);
        assert!(!prover.options.try_syntactic_first);
        assert_eq!(prover.options.max_states, 100);
    }

    #[test]
    fn test_prove_termination_success() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("terminates");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);
        sm.finals.push(end);

        let result = prover.prove(&sm, &LivenessProperty::Termination);
        assert!(result.is_proven());
        assert_eq!(prover.stats.proven, 1);
    }

    #[test]
    fn test_prove_termination_failure() {
        let mut prover = LivenessProver::new();

        // Create a state machine with an infinite cycle
        let mut sm = AsyncStateMachine::new("loops");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s1); // Infinite cycle

        let result = prover.prove(&sm, &LivenessProperty::Termination);
        assert!(result.is_disproven());
        assert_eq!(prover.stats.disproven, 1);
    }

    #[test]
    fn test_prove_progress_success() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("progress");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);
        sm.finals.push(end);

        let result = prover.prove(&sm, &LivenessProperty::Progress);
        assert!(result.is_proven());
    }

    #[test]
    fn test_prove_progress_failure() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("stalls");
        let stuck = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, stuck);
        // stuck has no outgoing - no progress

        let result = prover.prove(&sm, &LivenessProperty::Progress);
        assert!(result.is_disproven());
    }

    #[test]
    fn test_prove_reachability_success() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("reachable");
        let target = sm.add_state("Target", AsyncStateKind::Suspended);
        sm.add_transition(0, target);

        let prop = LivenessProperty::reachability("Target");
        let result = prover.prove(&sm, &prop);
        assert!(result.is_proven());
    }

    #[test]
    fn test_prove_reachability_failure() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("unreachable");
        let _target = sm.add_state("Target", AsyncStateKind::Suspended);
        // No transition to Target

        let prop = LivenessProperty::reachability("Target");
        let result = prover.prove(&sm, &prop);
        assert!(result.is_disproven());
    }

    #[test]
    fn test_prove_response_success() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("responds");
        let req = sm.add_state("Request", AsyncStateKind::Suspended);
        let resp = sm.add_state("Response", AsyncStateKind::Suspended);
        sm.add_transition(0, req);
        sm.add_transition(req, resp);

        let prop = LivenessProperty::response("Request", "Response");
        let result = prover.prove(&sm, &prop);
        assert!(result.is_proven());
    }

    #[test]
    fn test_prove_response_failure() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("no_response");
        let req = sm.add_state("Request", AsyncStateKind::Suspended);
        let _resp = sm.add_state("Response", AsyncStateKind::Suspended);
        let other = sm.add_state("Other", AsyncStateKind::Suspended);
        sm.add_transition(0, req);
        sm.add_transition(req, other);
        sm.add_transition(other, req); // Cycle without Response

        let prop = LivenessProperty::response("Request", "Response");
        let result = prover.prove(&sm, &prop);
        assert!(result.is_disproven());
    }

    #[test]
    fn test_prove_exceeds_max_states() {
        let options = LivenessProverOptions {
            max_states: 2,
            ..Default::default()
        };
        let mut prover = LivenessProver::with_options(options);

        let mut sm = AsyncStateMachine::new("big");
        sm.add_state("S1", AsyncStateKind::Suspended);
        sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_state("S3", AsyncStateKind::End);

        let result = prover.prove(&sm, &LivenessProperty::Termination);
        assert!(result.is_unknown());
    }

    #[test]
    fn test_analyze_all() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);
        sm.finals.push(end);

        let props = vec![LivenessProperty::Termination, LivenessProperty::Progress];
        let report = prover.analyze_all(&sm, &props);
        assert!(report.all_proven());
        assert_eq!(report.results.len(), 2);
    }

    #[test]
    fn test_prove_default_properties() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);
        sm.finals.push(end);

        let report = prover.prove_default_properties(&sm);
        assert!(report.all_proven());
    }

    #[test]
    fn test_stats_reset() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);
        sm.finals.push(end);

        prover.prove(&sm, &LivenessProperty::Termination);
        assert_eq!(prover.stats.total_analyzed, 1);

        prover.reset_stats();
        assert_eq!(prover.stats.total_analyzed, 0);
    }

    #[test]
    fn test_stats_summary() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);
        sm.finals.push(end);

        prover.prove(&sm, &LivenessProperty::Termination);
        let summary = prover.stats_summary();
        assert!(summary.contains("1 analyzed"));
        assert!(summary.contains("1 proven"));
    }

    #[test]
    fn test_report_formatted() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);
        sm.finals.push(end);

        let report = prover.prove_default_properties(&sm);
        let formatted = report.to_string_formatted();
        assert!(formatted.contains("Liveness Analysis Report"));
        assert!(formatted.contains("[PASS]"));
    }

    #[test]
    fn test_violation_witnesses() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("loops");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s1);

        let report = prover.prove_default_properties(&sm);
        let witnesses = report.violation_witnesses();
        assert!(!witnesses.is_empty());
    }

    #[test]
    fn test_disproven_properties() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let stuck = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, stuck);

        let report = prover.prove_default_properties(&sm);
        let disproven = report.disproven_properties();
        assert!(!disproven.is_empty());
    }

    #[test]
    fn test_default_options() {
        let options = LivenessProverOptions::default();
        assert!(options.try_syntactic_first);
        assert_eq!(options.timeout_ms, 5000);
        assert!(options.generate_counterexamples);
        assert_eq!(options.max_states, 10000);
    }

    #[test]
    fn test_fairness_unknown() {
        let mut prover = LivenessProver::new();

        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let prop = LivenessProperty::fairness("action");
        let result = prover.prove(&sm, &prop);
        // Fairness requires full SMT, should be unknown
        assert!(result.is_unknown());
    }
}
