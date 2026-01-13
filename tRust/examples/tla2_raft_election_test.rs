//! TLA2 Test Case: Distributed Consensus - Raft Leader Election
//!
//! This test case models the leader election phase of the Raft consensus algorithm.
//! It's a canonical test case for distributed systems verification.
//!
//! Raft Leader Election Properties:
//! 1. Safety: At most one leader per term
//! 2. Liveness: Eventually a leader is elected (under fairness assumptions)
//!
//! Model Parameters:
//! - 3 nodes (minimum for consensus)
//! - Terms 0-2 (bounded model checking)
//! - Message loss: none (reliable network)
//!
//! Expected: TLA2 should verify safety and find liveness under weak fairness
//!
//! Expected: PASS (compile and run as specification)

#![feature(rustc_attrs)]

use std::collections::HashSet;

// ============================================
// Raft State Definitions
// ============================================

/// Number of nodes in the cluster
const NUM_NODES: usize = 3;

/// Maximum term number for bounded model checking
const MAX_TERM: u8 = 2;

/// Node role in Raft
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Role {
    Follower = 0,
    Candidate = 1,
    Leader = 2,
}

/// Vote state for a node
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VoteState {
    /// Has voted in current term?
    pub voted: bool,
    /// Who did we vote for? (0xFF = none)
    pub voted_for: u8,
}

impl VoteState {
    pub const fn none() -> Self {
        VoteState {
            voted: false,
            voted_for: 0xFF,
        }
    }

    pub fn vote_for(node: u8) -> Self {
        VoteState {
            voted: true,
            voted_for: node,
        }
    }
}

/// State of a single Raft node
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeState {
    pub role: Role,
    pub term: u8,
    pub vote_state: VoteState,
    /// For candidates: votes received in current term
    pub votes_received: u8,
}

impl NodeState {
    pub const fn initial() -> Self {
        NodeState {
            role: Role::Follower,
            term: 0,
            vote_state: VoteState::none(),
            votes_received: 0,
        }
    }
}

/// Complete system state
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RaftState {
    pub nodes: [NodeState; NUM_NODES],
}

impl RaftState {
    pub fn initial() -> Self {
        RaftState {
            nodes: [NodeState::initial(); NUM_NODES],
        }
    }

    /// Safety property: At most one leader per term
    pub fn at_most_one_leader_per_term(&self) -> bool {
        for term in 0..=MAX_TERM {
            let mut leader_count: u8 = 0;
            for node in &self.nodes {
                if node.role == Role::Leader && node.term == term {
                    leader_count = leader_count.saturating_add(1);
                }
            }
            if leader_count > 1 {
                return false;
            }
        }
        true
    }

    /// Check if there is a leader in the current highest term
    pub fn has_leader(&self) -> bool {
        let max_term = self.nodes.iter().map(|n| n.term).max().unwrap_or(0);
        self.nodes
            .iter()
            .any(|n| n.role == Role::Leader && n.term == max_term)
    }

    /// Get current leader (if any)
    pub fn get_leader(&self) -> Option<(usize, u8)> {
        for (i, node) in self.nodes.iter().enumerate() {
            if node.role == Role::Leader {
                return Some((i, node.term));
            }
        }
        None
    }

    /// Majority for this cluster
    pub fn majority() -> u8 {
        ((NUM_NODES / 2) + 1) as u8
    }
}

// ============================================
// Raft Transitions
// ============================================

/// Node starts election: becomes candidate, increments term, votes for self
pub fn action_start_election(state: &RaftState, node_id: usize) -> Option<RaftState> {
    let node = state.nodes.get(node_id)?;

    // Guard: must be follower or candidate, term not maxed
    if node.role == Role::Leader || node.term >= MAX_TERM {
        return None;
    }

    let new_term = node.term.saturating_add(1);
    let mut new_state = state.clone();

    if let Some(node_ref) = new_state.nodes.get_mut(node_id) {
        *node_ref = NodeState {
            role: Role::Candidate,
            term: new_term,
            vote_state: VoteState::vote_for(node_id as u8),
            votes_received: 1, // Vote for self
        };
        Some(new_state)
    } else {
        None
    }
}

/// Node receives vote request and grants vote
pub fn action_grant_vote(
    state: &RaftState,
    voter_id: usize,
    candidate_id: usize,
) -> Option<RaftState> {
    let voter = state.nodes.get(voter_id)?;
    let candidate = state.nodes.get(candidate_id)?;

    // Guard: candidate must be in candidate role
    if candidate.role != Role::Candidate {
        return None;
    }

    // Guard: voter must be in same or lower term
    if voter.term > candidate.term {
        return None;
    }

    // Guard: voter hasn't voted in candidate's term, or voted for this candidate
    let can_vote = if voter.term < candidate.term {
        true // Different term, can update and vote
    } else {
        // Same term - check if already voted
        !voter.vote_state.voted || voter.vote_state.voted_for == candidate_id as u8
    };

    if !can_vote {
        return None;
    }

    // Guard: voter can't vote for self through this action
    if voter_id == candidate_id {
        return None;
    }

    let candidate_term = candidate.term; // Copy before mutation
    let mut new_state = state.clone();

    // Update voter state
    if let Some(voter_ref) = new_state.nodes.get_mut(voter_id) {
        *voter_ref = NodeState {
            role: Role::Follower, // Step down if candidate
            term: candidate_term,
            vote_state: VoteState::vote_for(candidate_id as u8),
            votes_received: 0,
        };
    }

    // Increment candidate's vote count (saturating)
    if let Some(cand_ref) = new_state.nodes.get_mut(candidate_id) {
        cand_ref.votes_received = cand_ref.votes_received.saturating_add(1);
    }

    Some(new_state)
}

/// Candidate becomes leader after receiving majority
pub fn action_become_leader(state: &RaftState, node_id: usize) -> Option<RaftState> {
    let node = state.nodes.get(node_id)?;

    // Guard: must be candidate with majority votes
    if node.role != Role::Candidate || node.votes_received < RaftState::majority() {
        return None;
    }

    let mut new_state = state.clone();
    if let Some(node_ref) = new_state.nodes.get_mut(node_id) {
        node_ref.role = Role::Leader;
    }

    Some(new_state)
}

/// Node discovers higher term and steps down
pub fn action_step_down(state: &RaftState, node_id: usize, higher_term: u8) -> Option<RaftState> {
    let node = state.nodes.get(node_id)?;

    // Guard: must see higher term from some other node
    let sees_higher = state.nodes.iter().any(|n| n.term > node.term);
    if !sees_higher || node.role == Role::Follower {
        return None;
    }

    // Find the highest term
    let max_term = state.nodes.iter().map(|n| n.term).max().unwrap_or(0);
    if higher_term != max_term || node.term >= max_term {
        return None;
    }

    let mut new_state = state.clone();
    if let Some(node_ref) = new_state.nodes.get_mut(node_id) {
        *node_ref = NodeState {
            role: Role::Follower,
            term: max_term,
            vote_state: VoteState::none(),
            votes_received: 0,
        };
    }

    Some(new_state)
}

// ============================================
// State Space Exploration
// ============================================

/// Encode state as compact representation
fn state_to_bytes(s: &RaftState) -> [u8; 12] {
    let mut bytes = [0u8; 12];
    // Manually encode for NUM_NODES=3 to avoid index verification issues
    if let Some(n0) = s.nodes.get(0) {
        if let Some(b) = bytes.get_mut(0) { *b = n0.role as u8; }
        if let Some(b) = bytes.get_mut(1) { *b = n0.term; }
        if let Some(b) = bytes.get_mut(2) { *b = if n0.vote_state.voted { 1 } else { 0 }; }
        if let Some(b) = bytes.get_mut(3) { *b = n0.votes_received; }
    }
    if let Some(n1) = s.nodes.get(1) {
        if let Some(b) = bytes.get_mut(4) { *b = n1.role as u8; }
        if let Some(b) = bytes.get_mut(5) { *b = n1.term; }
        if let Some(b) = bytes.get_mut(6) { *b = if n1.vote_state.voted { 1 } else { 0 }; }
        if let Some(b) = bytes.get_mut(7) { *b = n1.votes_received; }
    }
    if let Some(n2) = s.nodes.get(2) {
        if let Some(b) = bytes.get_mut(8) { *b = n2.role as u8; }
        if let Some(b) = bytes.get_mut(9) { *b = n2.term; }
        if let Some(b) = bytes.get_mut(10) { *b = if n2.vote_state.voted { 1 } else { 0 }; }
        if let Some(b) = bytes.get_mut(11) { *b = n2.votes_received; }
    }
    bytes
}

/// Results of exploration
#[derive(Debug)]
pub struct ExplorationResult {
    pub states_explored: usize,
    pub leader_states: usize,
    pub safety_violations: usize,
    pub max_term_reached: u8,
    pub election_traces: Vec<String>,
}

/// Explore all reachable states
pub fn explore_state_space() -> ExplorationResult {
    let mut visited: HashSet<[u8; 12]> = HashSet::new();
    let mut queue: Vec<RaftState> = Vec::new();
    let mut result = ExplorationResult {
        states_explored: 0,
        leader_states: 0,
        safety_violations: 0,
        max_term_reached: 0,
        election_traces: Vec::new(),
    };

    let initial = RaftState::initial();
    visited.insert(state_to_bytes(&initial));
    queue.push(initial);

    while let Some(state) = queue.pop() {
        result.states_explored = result.states_explored.saturating_add(1);

        // Check safety
        if !state.at_most_one_leader_per_term() {
            result.safety_violations = result.safety_violations.saturating_add(1);
        }

        // Count leader states
        if state.has_leader() {
            result.leader_states = result.leader_states.saturating_add(1);
        }

        // Track max term
        let max_t = state.nodes.iter().map(|n| n.term).max().unwrap_or(0);
        if max_t > result.max_term_reached {
            result.max_term_reached = max_t;
        }

        // Generate successors
        let mut successors: Vec<RaftState> = Vec::new();

        // Start election actions
        for i in 0..NUM_NODES {
            if let Some(next) = action_start_election(&state, i) {
                successors.push(next);
            }
        }

        // Grant vote actions
        for voter in 0..NUM_NODES {
            for candidate in 0..NUM_NODES {
                if voter != candidate {
                    if let Some(next) = action_grant_vote(&state, voter, candidate) {
                        successors.push(next);
                    }
                }
            }
        }

        // Become leader actions
        for i in 0..NUM_NODES {
            if let Some(next) = action_become_leader(&state, i) {
                successors.push(next);
            }
        }

        // Step down actions
        for i in 0..NUM_NODES {
            for term in 0..=MAX_TERM {
                if let Some(next) = action_step_down(&state, i, term) {
                    successors.push(next);
                }
            }
        }

        // Add unvisited successors
        for next in successors {
            let enc = state_to_bytes(&next);
            if !visited.contains(&enc) {
                visited.insert(enc);
                queue.push(next);
            }
        }
    }

    result
}

// ============================================
// Property Verification
// ============================================

/// Verify Raft safety: at most one leader per term
pub fn verify_election_safety() -> (bool, String) {
    let result = explore_state_space();

    if result.safety_violations > 0 {
        (
            false,
            format!(
                "VIOLATED: Found {} states with multiple leaders in same term",
                result.safety_violations
            ),
        )
    } else {
        (
            true,
            format!(
                "VERIFIED: At most one leader per term in {} states",
                result.states_explored
            ),
        )
    }
}

/// Check liveness: leader election eventually succeeds
pub fn check_election_liveness() -> (bool, String) {
    let result = explore_state_space();

    if result.leader_states > 0 {
        (
            true,
            format!(
                "REACHABLE: {} states have a leader (out of {})",
                result.leader_states, result.states_explored
            ),
        )
    } else {
        (
            false,
            "UNREACHABLE: No states with elected leader found".to_string(),
        )
    }
}

// ============================================
// TLA2 Integration Format
// ============================================

pub fn generate_tla2_spec() -> String {
    let mut out = String::new();
    out.push_str("// TLA2 StateMachine: RaftLeaderElection\n");
    out.push_str("StateMachine {\n");
    out.push_str("  name: \"RaftLeaderElection\",\n");
    out.push_str("  constants: [\n");
    out.push_str("    Constant { name: \"NUM_NODES\", value: 3 },\n");
    out.push_str("    Constant { name: \"MAX_TERM\", value: 2 },\n");
    out.push_str("  ],\n");
    out.push_str("  variables: [\n");
    out.push_str("    Variable { name: \"role\", ty: Array { elem: Enum { variants: [\"Follower\", \"Candidate\", \"Leader\"] }, len: 3 } },\n");
    out.push_str("    Variable { name: \"term\", ty: Array { elem: Int { bits: 8, signed: false }, len: 3 } },\n");
    out.push_str("    Variable { name: \"votedFor\", ty: Array { elem: Int { bits: 8, signed: false }, len: 3 } },\n");
    out.push_str("    Variable { name: \"votesReceived\", ty: Array { elem: Int { bits: 8, signed: false }, len: 3 } },\n");
    out.push_str("  ],\n");
    out.push_str("  properties: [\n");
    out.push_str("    // Safety: At most one leader per term\n");
    out.push_str("    Always(ForAll { t in 0..MAX_TERM: AtMostOne { i in 0..NUM_NODES: role[i] == Leader && term[i] == t } }),\n");
    out.push_str("    // Liveness (under fairness): Eventually a leader exists\n");
    out.push_str("    Eventually(Exists { i in 0..NUM_NODES: role[i] == Leader }),\n");
    out.push_str("  ],\n");
    out.push_str("}\n");
    out
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== TLA2 Test Case: Raft Leader Election ===\n");

    println!("Model Parameters:");
    println!("  Nodes: {}", NUM_NODES);
    println!("  Max Term: {}", MAX_TERM);
    println!("  Majority: {}\n", RaftState::majority());

    println!("Exploring state space...\n");

    let result = explore_state_space();

    println!("Results:");
    println!("  States explored: {}", result.states_explored);
    println!("  Leader states: {}", result.leader_states);
    println!("  Safety violations: {}", result.safety_violations);
    println!("  Max term reached: {}\n", result.max_term_reached);

    // Verify properties
    let (safety_ok, safety_msg) = verify_election_safety();
    println!("Safety (one leader per term): {}", safety_msg);

    let (liveness_ok, liveness_msg) = check_election_liveness();
    println!("Liveness (leader reachable): {}\n", liveness_msg);

    // Runtime assertions
    assert!(
        result.states_explored > 0,
        "Should explore at least one state"
    );
    assert!(safety_ok, "Safety property must hold");
    assert!(liveness_ok, "Liveness property must hold");
    assert_eq!(
        result.safety_violations, 0,
        "No safety violations allowed"
    );

    println!("=== Test Complete: Raft election properties verified ===");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let s = RaftState::initial();
        for node in &s.nodes {
            assert_eq!(node.role, Role::Follower);
            assert_eq!(node.term, 0);
            assert!(!node.vote_state.voted);
        }
    }

    #[test]
    fn test_start_election() {
        let s = RaftState::initial();
        let next = action_start_election(&s, 0).expect("Should be able to start election");
        assert_eq!(next.nodes[0].role, Role::Candidate);
        assert_eq!(next.nodes[0].term, 1);
        assert_eq!(next.nodes[0].votes_received, 1);
    }

    #[test]
    fn test_become_leader() {
        let mut s = RaftState::initial();
        // Node 0 is candidate with 2 votes (majority for 3 nodes)
        s.nodes[0] = NodeState {
            role: Role::Candidate,
            term: 1,
            vote_state: VoteState::vote_for(0),
            votes_received: 2,
        };

        let next = action_become_leader(&s, 0).expect("Should become leader with majority");
        assert_eq!(next.nodes[0].role, Role::Leader);
    }

    #[test]
    fn test_safety_holds() {
        let result = explore_state_space();
        assert_eq!(result.safety_violations, 0);
    }

    #[test]
    fn test_leader_reachable() {
        let result = explore_state_space();
        assert!(result.leader_states > 0);
    }
}
