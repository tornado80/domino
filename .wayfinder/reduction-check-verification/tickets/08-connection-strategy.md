---
title: Connection strategy between Rust and the Lean theorem
type: wayfinder:grilling
status: open
assignee:
blocked_by: ["04", "05", "07"]
---

## Question

Which strategy connects the Rust check to the Lean theorem: (a) translate the pure core with
Aeneas and prove in Lean that the translated code refines the abstract check, or (b) prove the
pure core with Verus or Creusot against a spec copy that is linked to the Lean spec by review?
Decide by comparing the two research results and the pure core stub. Record the trust base of
the selected strategy (what is still not verified).
