//! TLA2 Test Case: Async Race (Channel Send/Recv Timing)
//!
//! This test case demonstrates race conditions in channel-based communication
//! where the timing between send and receive operations can lead to unexpected
//! behavior.
//!
//! Scenario: Producer-Consumer with Bounded Channel
//! - Producer sends N items
//! - Consumer receives items
//! - Race: Producer may try to send when channel is full (blocking)
//!         Consumer may try to receive when channel is empty (blocking)
//!
//! With unbounded channel: different race where consumer reads before producer writes
//! With bounded channel: additional race of full/empty states
//!
//! Expected: TLA2 should explore all interleavings and verify safety properties
//!
//! Expected: PASS (compile and run as specification)

#![feature(rustc_attrs)]

// ============================================
// Channel State Machine
// ============================================

/// State of a bounded channel (capacity 2)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChannelState {
    /// Items in channel (0-2 for capacity 2)
    pub items: u8,
    /// Items successfully received by consumer
    pub consumed: u8,
    /// Producer state: items left to send
    pub producer_pending: u8,
    /// Is producer blocked on full channel?
    pub producer_blocked: bool,
    /// Is consumer blocked on empty channel?
    pub consumer_blocked: bool,
    /// Has producer finished?
    pub producer_done: bool,
    /// Has consumer finished?
    pub consumer_done: bool,
}

impl ChannelState {
    pub const CAPACITY: u8 = 2;
    pub const ITEMS_TO_SEND: u8 = 3;

    /// Initial state
    pub const fn initial() -> Self {
        ChannelState {
            items: 0,
            consumed: 0,
            producer_pending: Self::ITEMS_TO_SEND,
            producer_blocked: false,
            consumer_blocked: false,
            producer_done: false,
            consumer_done: false,
        }
    }

    /// Check if both parties are blocked (deadlock-like)
    pub fn is_both_blocked(&self) -> bool {
        self.producer_blocked && self.consumer_blocked
    }

    /// Check if system has completed successfully
    pub fn is_success(&self) -> bool {
        self.producer_done && self.consumer_done && self.consumed == Self::ITEMS_TO_SEND
    }

    /// Safety invariant: items never exceed capacity
    pub fn capacity_invariant(&self) -> bool {
        self.items <= Self::CAPACITY
    }

    /// Safety invariant: consumed never exceeds sent
    pub fn consumption_invariant(&self) -> bool {
        let sent = Self::ITEMS_TO_SEND.saturating_sub(self.producer_pending);
        self.consumed <= sent
    }
}

// ============================================
// Transitions (Actions)
// ============================================

/// Producer tries to send an item
pub fn action_producer_send(state: &ChannelState) -> Option<ChannelState> {
    // Guard: producer not done, not blocked, has items to send
    if state.producer_done || state.producer_blocked || state.producer_pending == 0 {
        return None;
    }

    if state.items < ChannelState::CAPACITY {
        // Can send: add item to channel (saturating to prevent overflow)
        Some(ChannelState {
            items: state.items.saturating_add(1),
            producer_pending: state.producer_pending.saturating_sub(1),
            // Unblock consumer if it was waiting
            consumer_blocked: false,
            ..*state
        })
    } else {
        // Channel full: block
        Some(ChannelState {
            producer_blocked: true,
            ..*state
        })
    }
}

/// Producer completes (all items sent)
pub fn action_producer_complete(state: &ChannelState) -> Option<ChannelState> {
    if !state.producer_done && state.producer_pending == 0 && !state.producer_blocked {
        Some(ChannelState {
            producer_done: true,
            ..*state
        })
    } else {
        None
    }
}

/// Consumer tries to receive an item
pub fn action_consumer_recv(state: &ChannelState) -> Option<ChannelState> {
    // Guard: consumer not done, not blocked
    if state.consumer_done || state.consumer_blocked {
        return None;
    }

    if state.items > 0 {
        // Can receive: take item from channel (saturating to prevent underflow)
        Some(ChannelState {
            items: state.items.saturating_sub(1),
            consumed: state.consumed.saturating_add(1),
            // Unblock producer if it was waiting
            producer_blocked: false,
            ..*state
        })
    } else if state.producer_done {
        // Channel empty and producer done - consumer can finish
        Some(ChannelState {
            consumer_done: true,
            ..*state
        })
    } else {
        // Channel empty, producer not done: block
        Some(ChannelState {
            consumer_blocked: true,
            ..*state
        })
    }
}

/// Consumer completes (producer done and channel empty)
pub fn action_consumer_complete(state: &ChannelState) -> Option<ChannelState> {
    if !state.consumer_done && state.producer_done && state.items == 0 {
        Some(ChannelState {
            consumer_done: true,
            ..*state
        })
    } else {
        None
    }
}

/// Wake up blocked producer (when consumer receives)
pub fn action_wake_producer(state: &ChannelState) -> Option<ChannelState> {
    if state.producer_blocked && state.items < ChannelState::CAPACITY {
        Some(ChannelState {
            producer_blocked: false,
            ..*state
        })
    } else {
        None
    }
}

/// Wake up blocked consumer (when producer sends)
pub fn action_wake_consumer(state: &ChannelState) -> Option<ChannelState> {
    if state.consumer_blocked && (state.items > 0 || state.producer_done) {
        Some(ChannelState {
            consumer_blocked: false,
            ..*state
        })
    } else {
        None
    }
}

// ============================================
// State Space Exploration
// ============================================

type Action = fn(&ChannelState) -> Option<ChannelState>;

const ALL_ACTIONS: [Action; 6] = [
    action_producer_send,
    action_producer_complete,
    action_consumer_recv,
    action_consumer_complete,
    action_wake_producer,
    action_wake_consumer,
];

#[allow(dead_code)] // Reserved for future trace output
const ACTION_NAMES: [&str; 6] = [
    "producer_send",
    "producer_complete",
    "consumer_recv",
    "consumer_complete",
    "wake_producer",
    "wake_consumer",
];

/// Encode state as u32 for tracking
fn state_to_u32(s: &ChannelState) -> u32 {
    let mut v: u32 = 0;
    v |= (s.items as u32) << 24;
    v |= (s.consumed as u32) << 20;
    v |= (s.producer_pending as u32) << 16;
    v |= if s.producer_blocked { 1 } else { 0 } << 12;
    v |= if s.consumer_blocked { 1 } else { 0 } << 8;
    v |= if s.producer_done { 1 } else { 0 } << 4;
    v |= if s.consumer_done { 1 } else { 0 };
    v
}

/// Decode state from u32
fn u32_to_state(v: u32) -> ChannelState {
    ChannelState {
        items: ((v >> 24) & 0xF) as u8,
        consumed: ((v >> 20) & 0xF) as u8,
        producer_pending: ((v >> 16) & 0xF) as u8,
        producer_blocked: ((v >> 12) & 0x1) == 1,
        consumer_blocked: ((v >> 8) & 0x1) == 1,
        producer_done: ((v >> 4) & 0x1) == 1,
        consumer_done: (v & 0x1) == 1,
    }
}

/// Result of state space exploration
#[derive(Debug)]
pub struct ExplorationResult {
    pub states_explored: usize,
    pub success_states: usize,
    pub deadlock_states: usize,
    pub invariant_violations: usize,
    pub race_conditions: Vec<(u32, String)>, // state, description
}

/// Explore all reachable states
pub fn explore_state_space() -> ExplorationResult {
    use std::collections::HashSet;

    let mut visited: HashSet<u32> = HashSet::new();
    let mut queue: Vec<u32> = Vec::new();
    let mut result = ExplorationResult {
        states_explored: 0,
        success_states: 0,
        deadlock_states: 0,
        invariant_violations: 0,
        race_conditions: Vec::new(),
    };

    let initial = ChannelState::initial();
    let initial_enc = state_to_u32(&initial);
    visited.insert(initial_enc);
    queue.push(initial_enc);

    while let Some(state_enc) = queue.pop() {
        result.states_explored = result.states_explored.saturating_add(1);
        let state = u32_to_state(state_enc);

        // Check properties
        if state.is_success() {
            result.success_states = result.success_states.saturating_add(1);
        }

        if state.is_both_blocked() {
            result.deadlock_states = result.deadlock_states.saturating_add(1);
        }

        if !state.capacity_invariant() || !state.consumption_invariant() {
            result.invariant_violations = result.invariant_violations.saturating_add(1);
        }

        // Race condition: consumer blocked when items exist
        if state.consumer_blocked && state.items > 0 {
            result
                .race_conditions
                .push((state_enc, "Consumer blocked with items available".to_string()));
        }

        // Race condition: producer blocked when space exists
        if state.producer_blocked && state.items < ChannelState::CAPACITY {
            result
                .race_conditions
                .push((state_enc, "Producer blocked with space available".to_string()));
        }

        // Try all actions
        for (i, action) in ALL_ACTIONS.iter().enumerate() {
            if let Some(next) = action(&state) {
                let next_enc = state_to_u32(&next);
                if !visited.contains(&next_enc) {
                    visited.insert(next_enc);
                    queue.push(next_enc);
                }
            }
            let _ = i; // suppress warning
        }
    }

    result
}

/// Verify safety properties
pub fn verify_safety() -> (bool, String) {
    let result = explore_state_space();

    if result.invariant_violations > 0 {
        return (
            false,
            format!("Invariant violated in {} states", result.invariant_violations),
        );
    }

    if result.deadlock_states > 0 {
        return (
            false,
            format!(
                "Found {} deadlock states (both blocked)",
                result.deadlock_states
            ),
        );
    }

    (true, "Safety properties verified".to_string())
}

/// Check liveness: eventually success
pub fn check_liveness() -> (bool, String) {
    let result = explore_state_space();

    if result.success_states == 0 {
        return (
            false,
            "No successful terminal states found".to_string(),
        );
    }

    (
        true,
        format!(
            "Liveness: {} success states reachable",
            result.success_states
        ),
    )
}

// ============================================
// TLA2 Integration Format
// ============================================

pub fn generate_tla2_spec() -> String {
    let mut out = String::new();
    out.push_str("// TLA2 StateMachine: AsyncChannelRace\n");
    out.push_str("StateMachine {\n");
    out.push_str("  name: \"AsyncChannelRace\",\n");
    out.push_str("  variables: [\n");
    out.push_str("    Variable { name: \"items\", ty: Int { bits: 8, signed: false } },\n");
    out.push_str("    Variable { name: \"consumed\", ty: Int { bits: 8, signed: false } },\n");
    out.push_str("    Variable { name: \"producer_pending\", ty: Int { bits: 8, signed: false } },\n");
    out.push_str("    Variable { name: \"producer_blocked\", ty: Bool },\n");
    out.push_str("    Variable { name: \"consumer_blocked\", ty: Bool },\n");
    out.push_str("    Variable { name: \"producer_done\", ty: Bool },\n");
    out.push_str("    Variable { name: \"consumer_done\", ty: Bool },\n");
    out.push_str("  ],\n");
    out.push_str("  invariants: [\n");
    out.push_str("    // items <= CAPACITY\n");
    out.push_str("    Compare(Var(\"items\"), Le, Lit(2)),\n");
    out.push_str("    // consumed <= sent\n");
    out.push_str("    Compare(Var(\"consumed\"), Le, BinOp(Lit(3), Sub, Var(\"producer_pending\"))),\n");
    out.push_str("  ],\n");
    out.push_str("  properties: [\n");
    out.push_str("    // Safety: never both blocked (deadlock)\n");
    out.push_str("    Always(Not(And(Var(\"producer_blocked\"), Var(\"consumer_blocked\")))),\n");
    out.push_str("    // Liveness: eventually success\n");
    out.push_str("    Eventually(And(Var(\"producer_done\"), Var(\"consumer_done\"))),\n");
    out.push_str("  ],\n");
    out.push_str("}\n");
    out
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== TLA2 Test Case: Async Race (Channel Send/Recv) ===\n");

    println!("Scenario:");
    println!("  Bounded channel (capacity 2)");
    println!("  Producer sends 3 items");
    println!("  Consumer receives items");
    println!("  Possible races: send-on-full, recv-on-empty\n");

    println!("Exploring state space...\n");

    let result = explore_state_space();

    println!("States explored: {}", result.states_explored);
    println!("Success states: {}", result.success_states);
    println!("Deadlock states: {}", result.deadlock_states);
    println!("Invariant violations: {}", result.invariant_violations);
    println!("Race conditions found: {}\n", result.race_conditions.len());

    // Report race conditions
    if !result.race_conditions.is_empty() {
        println!("Race condition examples:");
        for (enc, desc) in result.race_conditions.iter().take(3) {
            let s = u32_to_state(*enc);
            println!(
                "  - {} (items={}, consumed={}, pending={})",
                desc, s.items, s.consumed, s.producer_pending
            );
        }
        println!();
    }

    // Verify properties
    let (safety_ok, safety_msg) = verify_safety();
    println!("Safety: {} - {}", if safety_ok { "PASS" } else { "FAIL" }, safety_msg);

    let (liveness_ok, liveness_msg) = check_liveness();
    println!("Liveness: {} - {}", if liveness_ok { "PASS" } else { "FAIL" }, liveness_msg);

    // Runtime assertions for test framework
    assert!(result.states_explored > 0, "Should explore states");
    assert!(result.success_states > 0, "Should have success states");
    assert_eq!(result.invariant_violations, 0, "Should not violate invariants");
    // Note: deadlock states may or may not exist depending on model
    // Our model allows wake-up actions to prevent permanent deadlock

    println!("\n=== Test Complete ===");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let s = ChannelState::initial();
        assert_eq!(s.items, 0);
        assert_eq!(s.consumed, 0);
        assert_eq!(s.producer_pending, ChannelState::ITEMS_TO_SEND);
        assert!(!s.producer_blocked);
        assert!(!s.consumer_blocked);
    }

    #[test]
    fn test_invariants_hold() {
        let result = explore_state_space();
        assert_eq!(result.invariant_violations, 0);
    }

    #[test]
    fn test_success_reachable() {
        let result = explore_state_space();
        assert!(result.success_states > 0);
    }

    #[test]
    fn test_state_encoding() {
        let s = ChannelState::initial();
        let enc = state_to_u32(&s);
        let dec = u32_to_state(enc);
        assert_eq!(s.items, dec.items);
        assert_eq!(s.consumed, dec.consumed);
        assert_eq!(s.producer_pending, dec.producer_pending);
    }
}
