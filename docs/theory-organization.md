# HOL Theory Organization

This document records the intended naming and layering conventions for HOL4
script theories in this repository.  The whole tree does not follow these
conventions yet; we are applying them progressively as files are cleaned up.

## Theory roles

### `*Defs`

Definition theories contain datatypes, functions, predicates, and small
syntax-level helpers.  They should avoid heavy semantic or pass-correctness
proofs.

Examples: `cfgTransformDefs`, `dfgDefs`.

### `*Props`

Property theories are the public interface for stable, generally useful facts
about definitions.  Public theorem names should be owned here when the facts are
interface-level facts for downstream developments.

`*Props` should not merely be a layer of exact `ACCEPT_TAC` aliases for theorems
proved elsewhere.  Prefer proving short facts directly in `*Props`.  If a public
fact needs substantial proof engineering, put technical helpers in a workhorse
proof theory and prove the final public statement in `*Props` with a short proof.

### `*Proofs`

Proof theories contain workhorse and technical lemmas: induction helpers,
case-specific invariants, proof decomposition facts, and facts with less stable
or more implementation-oriented names.  These theorems may still be exported and
useful; the distinction is by theory role and theorem name, not by making every
helper `[local]`.

`*Proofs` should not duplicate public theorem names already owned by `*Props`.
It is acceptable for a proof theory to depend on the corresponding props theory
when technical lemmas build on public facts.

### `*Correct`, `*Sound`, `*Equiv`

Top-level correctness/equivalence theories should expose the main semantic
correctness statements for passes or transformations, with supporting machinery
kept in defs/props/proofs layers as appropriate.

## Theorem naming

Use short, descriptive names for stable public facts, for example:

```sml
fn_labels_replace_block
lookup_block_replace_eq
wf_function_remove_block
```

Avoid mechanical `_proof` suffixes for facts that are meant to be consumed as
ordinary theorems.  If a theorem is technical, name the technical role instead,
e.g. `foo_step_case`, `foo_ind`, or `foo_aux`.

## Re-export policy

Avoid exact theorem re-exports like:

```sml
Theorem foo:
  ...same statement...
Proof
  ACCEPT_TAC someProofsTheory.foo_proof
QED
```

This creates duplicate names for one concept and obscures which theory owns the
interface.  Prefer one of:

1. prove `foo` directly in the appropriate `*Props` theory;
2. prove helper lemmas in `*Proofs`, then prove `foo` in `*Props` with a short
   proof using those helpers;
3. if no presentation layer is needed, expose the theorem only once from its
   natural theory.

## Imports and qualifications

A theory that uses public facts should list the corresponding `*Props` theory in
`Ancestors`.  During refactors, qualified references such as
`cfgTransformPropsTheory.foo` may be useful to make dependency migration
explicit.  Once imports are settled, unqualified use is acceptable when it is
clear and unambiguous.

Technical facts should continue to come from the relevant `*Proofs` theory.

## Current model

`cfgTransformProps` / `cfgTransformProofs` is the current model cleanup:

- `cfgTransformProps` owns the stable public facts about CFG transformation
  operations.
- `cfgTransformProofs` contains technical extras and depends on
  `cfgTransformProps` rather than duplicating its public theorem names.
