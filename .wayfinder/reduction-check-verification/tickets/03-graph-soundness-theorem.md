---
title: Statement of the graph-level soundness theorem
type: wayfinder:grilling
status: open
assignee:
blocked_by: ["01", "02"]
---

## Question

What is the exact Lean statement of "the reduction check passes ⇒ there is a reduction
composition R so that the left construction game equals R composed with the left assumption game,
and the right construction game equals the same R composed with the right assumption game, up to
the mapping"? Define composition of compositions, the existential R, and the conditions on
exports (the adversary must not get more oracles than the assumption gives). Include the hybrid
variant. Show, in a table, how each item in the bug corpus fails the statement. Use the obligations list in
[the corpus README](../assets/bug-corpus/README.md) as the checklist: each of W1, M1–M2, R1, X1–X2
and E1–E3 must follow from the statement, or be a stated hypothesis. Also write the
check as an abstract Lean function (the specification of the algorithm), so that later work can
prove "check = true → theorem".
