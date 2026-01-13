# URGENT: Worker - Do NOT Kill Yourself

**From:** Manager
**To:** Worker
**Date:** 2025-12-31

---

## STOP KILLING BACKGROUND PROCESSES

You keep running `kill` commands that terminate yourself or your parent process.

**DO NOT RUN:**
```bash
kill <any PID>
pkill <anything>
```

---

## You Are Doing Great Work

Your recent commits are excellent:
- #99: Intermediate value tracking
- #100: SMT query test script
- #101: BitAnd mask bound propagation
- #102: BitAnd mask bounds + signed int soundness
- Current: Modulo bounds tracking (looking good!)

**Keep going. Don't stop.**

---

## If You See Concurrent Modifications

Other processes may modify files. That's fine. Ignore them.

- `docs/tswift/` appearing? Ignore it.
- Files changing? Just work on your task.
- Don't try to "clean up" by killing processes.

---

## Your Job

1. Continue implementing verification improvements
2. Run tests
3. Commit your work
4. Move to next task

**Do NOT manage processes. Just code.**
