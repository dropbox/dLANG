# TLA2 Performance Benchmarks

**Version**: 1.0.0
**Date**: 2026-01-03
**Status**: Response to TLA2_RESPONSE.md Section "What We Need From You" #3

This document provides performance benchmarks from tRust's TLA2 test cases, answering the TLA2 team's questions about realistic workload sizes.

---

## Summary

The following benchmarks represent typical state space sizes for async Rust verification:

| Test Case | States Explored | Processes/Nodes | Trace Depth | Property |
|-----------|-----------------|-----------------|-------------|----------|
| Two-Mutex Deadlock | 8 | 2 | 3 | Safety (deadlock-free) |
| Async Channel Race | 20 | 2 | ~10 | Safety + Liveness |
| Raft Leader Election | 1,586,541 | 3 | Variable | Safety + Liveness |

**Key Finding**: Real-world distributed systems verification (like Raft) can easily produce 1M+ states even with minimal parameters (3 nodes, 2 terms).

---

## Detailed Benchmark Results

### 1. Two-Mutex Deadlock

**File**: `examples/tla2_mutex_deadlock_test.rs`

**Scenario**: Classic deadlock pattern where two processes acquire two mutexes in opposite order.

**Results**:
```
States explored: 8
Deadlock found: true
Counterexample trace depth: 3 steps
```

**State Space Characteristics**:
- Variables: 4 (process_a state, process_b state, mutex1 owner, mutex2 owner)
- Process states: 4 each (Start, HoldFirst, HoldBoth, Done)
- Mutex states: 3 each (Free, HeldByA, HeldByB)
- Theoretical max: 4 * 4 * 3 * 3 = 144 (actual reachable: 8)
- Actions: 6

**TLA2 Relevance**:
- Small state space, fast to explore
- Deadlock found quickly via BFS
- Good for regression testing

---

### 2. Async Channel Race

**File**: `examples/tla2_async_race_test.rs`

**Scenario**: Producer-consumer with bounded channel (capacity 2), 3 items to send.

**Results**:
```
States explored: 20
Success states: 2
Deadlock states: 0
Invariant violations: 0
Race conditions found: 0
Safety: PASS
Liveness: PASS
```

**State Space Characteristics**:
- Variables: 7 (items, consumed, producer_pending, producer_blocked, consumer_blocked, producer_done, consumer_done)
- Channel capacity: 2
- Items to send: 3
- Actions: 6 (send, recv, complete, wake)

**TLA2 Relevance**:
- Demonstrates async/await modeling
- Tests both safety and liveness
- Wake-up actions prevent spurious deadlock

---

### 3. Raft Leader Election

**File**: `examples/tla2_raft_election_test.rs`

**Scenario**: Raft consensus leader election with 3 nodes, bounded to term 2.

**Results**:
```
States explored: 1,586,541
Leader states: 786,378
Safety violations: 0
Max term reached: 2
Safety (one leader per term): VERIFIED
Liveness (leader reachable): REACHABLE
```

**State Space Characteristics**:
- Variables per node: 4 (role, term, votedFor, votesReceived)
- Node count: 3
- Max term: 2
- Role states: 3 (Follower, Candidate, Leader)
- Actions: ~15 (start election, grant vote, become leader, step down)

**TLA2 Relevance**:
- **This is the primary benchmark for distributed systems verification**
- 1.5M states in a minimal configuration
- Scaling: 5 nodes with 3 terms would produce ~100M+ states
- Demonstrates need for symmetry reduction, DPOR

---

## Workload Sizing Guidance

### Question 1: Typical number of states?

| Workload Type | Typical States | Notes |
|---------------|----------------|-------|
| Unit test (single async fn) | 10-100 | Trivial exploration |
| Concurrent primitives (mutex/channel) | 100-10K | Interleaving grows quickly |
| Small distributed protocol (3 nodes) | 100K-10M | Depends on message complexity |
| Medium distributed protocol (5 nodes) | 10M-1B | Requires optimization |
| Full Raft (5 nodes, unbounded terms) | Unbounded | Needs compositional verification |

### Question 2: Typical number of processes/threads?

| Application Type | Processes/Threads | Notes |
|------------------|-------------------|-------|
| Web server handler | 1-2 | Request + background task |
| Database connection pool | 5-10 | Pool workers + coordinator |
| Distributed system (minimal) | 3 | Consensus quorum minimum |
| Distributed system (typical) | 5-7 | Production configurations |
| Microservices integration | 10+ | Each service = 1 process |

### Question 3: Typical trace depth?

| Bug Type | Typical Trace Depth | Notes |
|----------|---------------------|-------|
| Simple race condition | 3-5 | Two concurrent accesses |
| Deadlock (2 locks) | 3-4 | Interleaved lock acquisition |
| Livelock | 10-50 | Repeated failed attempts |
| Distributed consensus bug | 10-100 | Multi-round protocol |
| Byzantine failure | 20-200 | Adversarial interleavings |

---

## Scaling Projections

Based on our Raft benchmark (1.58M states for 3 nodes, 2 terms):

```
Expected state space growth:
  3 nodes, 2 terms:     1,586,541 states (measured)
  3 nodes, 3 terms:    ~15,000,000 states (estimated)
  5 nodes, 2 terms:   ~200,000,000 states (estimated)
  5 nodes, 3 terms: ~2,000,000,000 states (estimated)
```

**Mitigation strategies needed**:
1. **Symmetry reduction**: 3-5x reduction for identical nodes
2. **Partial-order reduction**: 10-100x reduction for independent actions
3. **Compositional verification**: Verify subsystems separately
4. **Bounded model checking**: Limit trace depth

---

## Performance Targets for tRust Integration

Based on typical use cases, tRust needs TLA2 to handle:

| Scenario | Target Time | States | Notes |
|----------|-------------|--------|-------|
| CI check (quick) | < 10s | < 1M | Every commit |
| CI check (full) | < 60s | < 50M | Nightly builds |
| Development iteration | < 5s | < 100K | Developer feedback loop |
| Full verification | < 10min | < 500M | Release verification |

**Critical path**: Development iteration speed. Developers need sub-5-second feedback to stay in flow.

---

## Test Case Source Locations

All test cases are runnable Rust programs that perform explicit state space exploration:

1. `examples/tla2_mutex_deadlock_test.rs` - Two-mutex deadlock detection
2. `examples/tla2_async_race_test.rs` - Async channel race conditions
3. `examples/tla2_raft_election_test.rs` - Raft leader election consensus

Run with nightly Rust:
```bash
rustup run nightly rustc examples/tla2_mutex_deadlock_test.rs -o tla2_mutex && ./tla2_mutex
rustup run nightly rustc examples/tla2_async_race_test.rs -o tla2_async && ./tla2_async
rustup run nightly rustc examples/tla2_raft_election_test.rs -o tla2_raft && ./tla2_raft
```

---

## Next Steps

1. **TLA2 team**: Use these benchmarks to validate performance targets
2. **TLA2 team**: Prioritize symmetry reduction for distributed systems (3-5 identical nodes)
3. **tRust team**: Will provide additional benchmarks as real-world crates are validated
4. **Both teams**: Coordinate on compositional verification for unbounded protocols

---

## Contact

- tRust repository: https://github.com/dropbox/dLANG/tRust
- TLA2 repository: https://github.com/dropbox/tla2
- Related documents:
  - `TLA2_STATEMACHINE_SPEC.md` - Format specification
  - `TLA2_RESPONSE.md` - TLA2 team API specification
