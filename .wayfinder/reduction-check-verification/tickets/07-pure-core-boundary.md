---
title: Pure core boundary of the Rust reduction check
type: wayfinder:prototype
status: open
assignee:
blocked_by: ["02", "04", "09"]
---

## Question

What is the boundary between the parser and a pure reduction check in Rust: input types (a
simple representation of compositions, game instances, and mappings, without pest `Pair` or
miette spans), output type (verdict plus an error enum that the parser converts into
diagnostics), and the function signatures? Make a rough stub (types and signatures only, in a
throwaway branch or an asset) that follows the Lean data model and the Aeneas restrictions. React
to it with the user, and record the refactor plan.
