---
title: Aeneas and Charon support for the reduction core
type: wayfinder:research
status: open
assignee:
blocked_by: []
---

## Question

What is the Rust subset that Charon and Aeneas can translate to Lean today (closures, iterator
chains, `HashMap`/`HashSet`, `Vec` indexing, `String` comparison, recursion, `Result` with error
enums, lifetimes, trait objects)? What does the Lean output look like, and how is it maintained when
the Rust code changes? Give examples of projects that use it at a similar scale. Then state the
restrictions that a pure reduction core must obey to translate. Write a markdown summary as an asset.
