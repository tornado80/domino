---
title: Code base that is the target of verification
type: wayfinder:grilling
status: open
assignee:
blocked_by: []
---

## Question

Which Rust code is the target of the verification work: the current `src/parser/reduction.rs`
(commit `7bf2632b`), or the refactor of the reduction check in PR #1 of `grittygrease/domino`, with the
fixes of PR #2 on top? Is the plan to merge those PRs first (and with which review), or to fix the check
again from the Lean statement? The answer fixes the base of the pure core boundary, and it tells if the
corpus verdicts must be measured again on the new code.
