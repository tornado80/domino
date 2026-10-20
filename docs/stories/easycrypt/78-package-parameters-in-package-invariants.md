# Story 78 — Package parameters in package invariants (`<Pkg>_pkgparams`)

**Epic:** EasyCrypt Export — read `docs/stories/easycrypt/00-overview.md` first.
**Branch:** `amir/easycrypt-export`
**Depends on:** 77.
**Blocks:** 79, 80.
**ADR:** 0019 (point 1).
**Decisions:** grilling of 2026-10-20/21, Questions 1, 2, 3, 6 and 8.

A **translation** story, Rust only. Test-first.

---

## 1. Why this story exists

Since merge `3662315a` the prover binds `pkg.<param>` in a package invariant (`gen_varbinding`
with `"pkg"`, `smtrewrite.rs`), and `(pkg.<fn param> …)` as a `<<func-…>>` alias. Translation
binds only `pkg.<state field>` (`invariant/side.rs`, `package_templates`), so such a file stops with
`InvariantError::Unrecognised`. Story 58's fact "`pkg.<name>` binds only the state fields" is stale.

## 2. Inherited

- Story 69: `<Pkg>_pkgstate`, declared by the first variant (`StateOwners`).
- Story 73: the template `PkgInv_<N>_of_<P>` and the wrapper `PkgInv_<N>_of_<I>_in_<C>` (ADR 0018).
- Story 76: the package lemma files `PkgInv_<V>_<O>`, `Frame_<V>_<O>`, `PkgInv_<V>_init`
  (`pkginv.rs`), which apply the template to a state literal of the variant.
- Story 77: the bottom-up proof (`sideinv/bottom_up.rs`), which applies the templates too.

## 3. Work to do

### 3.1 The record

`type <P>_pkgparams = { <P>_param_<p> : <ty>; … }`, one field for each parameter of package `P`
that the variant does not bake into a type: every Bool, every Integer that
`package::param_needs_var` keeps, and every function parameter. Same owner and file as
`<P>_pkgstate` (`StateOwners`). A package with no such parameter has no record. The field prefix
`_param_` keeps the field names apart from the `<P>_pkgstate` fields (two record types in one file
cannot share a field name, `invariant.rs:231`).

### 3.2 The template

`op PkgInv_<N>_of_<P> (p : <P>_pkgparams) (s : <P>_pkgstate) : bool`. Without a params record the
template keeps its one argument; without state (`side.rs:65`) it takes `p` only. The owner module
decides this itself; no caller passes a flag.

In the body:
- `pkg.<p>` for a value parameter → ``p.`<P>_param_<p>``;
- `(pkg.<f> a …)` for a function parameter → ``p.`<P>_param_<f> a …``.

### 3.3 The literals

Each place that applies a template builds the params literal too:
- the package lemma files (`pkginv.rs`): value fields read the variant's module variables
  (`<V>.<p>`); function fields are the variant's operator, `func_op_name(<bound theorem const>)`;
- the wrapper `PkgInv_<N>_of_<I>_in_<C> (s : <C>_side)` has no memory, so it can only read the
  parameters from the side record. This story adds the field `<C>_params_<I> : <P>_pkgparams` to
  `<C>_side` for each instance whose package has a params record (`composition_items`), and the
  wrapper passes ``s.`<C>_params_<I>``. `side_inv_app` (`proof.rs`) fills the field: value fields
  from the instance's module variables (`Comp_<C>.Pkg_Inst_<I>.<p>`, with the memory tag), function
  fields from the operator of the bound theorem constant;
- the bottom-up proof (`sideinv/bottom_up.rs:145`).

### 3.4 Rejected alternatives (ADR 0019)

- Parameters as fields of `<P>_pkgstate`: breaks *equal state*.
- One positional argument for each parameter: change amplification at every caller.
- One template for each variant when the body reads a function parameter; an error when variants
  differ.

## 4. Tests first

New project `test-projects/test-package-invariant-params`: package `P` with `b : Bool`,
`k : Integer` (a value, not a width) and `f : fn …`; two game instances whose `P` instances bind `f`
to two different theorem constants (two variants); `(define-package-invariant main …)` that reads
`pkg.b`, `pkg.k` and `(pkg.f …)`; one package without such parameters, whose template must not
change.

Write these red first:
- [ ] `domino prove` accepts the project (the prover semantics hold).
- [ ] Text: one `type P_pkgparams = {` with the three fields; `op PkgInv_main_of_P (p : P_pkgparams) (s : P_pkgstate)`;
      the other package's template keeps one argument.
- [ ] Text: each variant's package lemma applies the template to its own function operator.
- [ ] Text: `<C>_side` has `<C>_params_P : P_pkgparams`, the wrapper passes it, and the
      `side_inv_<C>` literal of a side lemma reads `Comp_<C>.Pkg_Inst_P.b`.
- [ ] A side-invariant job of a composition with `P` has 0 admits (skips without `DOMINO_EASYCRYPT`).
- [ ] Compile of the full tree (skips without `easycrypt`).
- [ ] A package-invariant job of `P` has 0 admits (skips without `DOMINO_EASYCRYPT`).

## 5. Acceptance criteria

- [ ] All tests of §4 green; the existing goldens change only where a template gains `p`.
- [ ] CRAP gate of `implement` on the diff: no touched function over budget.
- [ ] `cargo build/test/clippy --workspace`, with and without `--features cvc5-lib`: clean.
