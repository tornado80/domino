# Invariant operator names are joined with `_of_` and `_in_`, with `_` doubled inside each part

**Status:** accepted. Implemented by
`docs/stories/easycrypt/73-named-invariants-in-easycrypt-and-the-debugger.md`. Grilling of
2026-10-12/20, Questions 3, 3a and 3b.

Package and game invariants now have names, and an owner can declare several
(`(define-package-invariant main …)`, on `main` since `f1f22011`). Translation needs one EasyCrypt
operator for each of them. A plain `_` join is not one-to-one: package `A_B` with invariant `c` and
package `A` with invariant `B_c` both give `PkgInv_A_B_c`. In one file that is a hard error today
(`OpNameCollision`). Across two imported files EasyCrypt chooses an overloaded operator by type
without a message (`easycrypt/src/ecTyping.ml`, `MultipleOpMatch` only when both fit), and
`rewrite /PkgInv_A_B_c` depends on the same choice. The owner wants no new rule in the Domino
language.

We decided:

1. **The names:**
   - the template, in the package file: `PkgInv_<N>_of_<P>`;
   - the wrapper for one instance, in the composition file: `PkgInv_<N>_of_<I>_in_<C>`;
   - the game invariant, in the composition file: `GameInv_<N>_of_<C>`;
   - `side_inv_<C>` does not change.
2. **Inside each part, every `_` is written `__`.** `<N>` is first mapped by the existing
   `mangle_smt_def_name`. Then every run of `_` inside a part has an even length, and the separator
   `_of_` always makes the first run of odd length, so the parts can always be read back. A template
   can never equal a wrapper, because `_in_` makes odd runs and an escaped package name has none.
   The usual names do not change: `PkgInv_main_of_Prf`, `GameInv_main_of_Hybrid2`. Invariant
   `key_table` of package `Key_Store` becomes `PkgInv_key__table_of_Key__Store`.
3. **A reference to another file always uses the full name** (`Comp_<C>.PkgInv_…`), as it does
   today, and never depends on an import.
4. **What stays a hard error** is what `mangle_smt_def_name` already cannot tell apart inside one
   owner: two invariant names that differ only by `-` and `_` (`my-inv`, `my_inv`), as for state
   relations today.

## Considered options

- **A flat `_` join and the hard error.** The error comes far from where the name is declared, and
  a clash between two imported files is never detected.
- **`_of_` with a language rule "an invariant name must not contain `_of_`".** One-to-one and
  readable, but the owner wants no new language rule.
- **Nested theories** (`theory PkgInv_Prf. op main …`, used as `Comp_C.PkgInv_Prf.main`). One-to-one
  without a rule, but longer names in goals, a new output construct, and a template theory and a
  wrapper theory that clash on import unless their prefixes differ.
- **Numbers** (`PkgInv_Prf_1`). The name is lost, and reordering the invariants renames them.
- **A suffix on a clash** (`_2`). A name would depend on which other packages exist, so adding a
  package could rename an operator that a saved session refers to.

## Consequences

- Names with `_` in a part look doubled in goals. That is the price of having no language rule.
- A test reads every generated name back to its parts.
- Proof files and session records from before the change name the old operators, and are stale.
