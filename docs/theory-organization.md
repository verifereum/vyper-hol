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

## Current cleanup status

`cfgTransformProps` / `cfgTransformProofs` is the completed model cleanup:

- `cfgTransformProps` owns the stable public facts about CFG transformation
  operations.
- `cfgTransformProofs` contains technical extras and depends on
  `cfgTransformProps` rather than duplicating its public theorem names.

`venomMemProps` / `venomMemProofs` is partially migrated:

- `venomMemProps` is the public interface for stable memory facts and no longer
  uses exact `ACCEPT_TAC` re-export wrappers.
- Consumers touched during cleanup now use `venomMemProps` for public alloca and
  memory facts rather than referring directly to `venomMemProofsTheory.*_proof`
  names.
- Common bytes32 facts such as `dimindex_256` and
  `word_bytes_roundtrip_256` are consolidated in `venomMemProps`; several
  pass-local duplicates have been deleted.
- `venomMemProofs` still contains transitional `_proof` source theorems used to
  derive the public `venomMemProps` interface.  Future cleanup should move proof
  bodies or expose more precisely named technical helpers so these duplicate
  public concepts can be removed.

Small proof-only layers have been folded away where they only contained public
facts and had no independent technical role:

- `memLocProofs` was folded into `memLocProps`.
- `latticeProofs` was folded into `latticeProps`.
- `dfIterateProps` now owns public iterate corollaries directly; the remaining
  `dfIterateProofs` facts are technical orbit/step lemmas used by other proofs.

When a theorem looks more general than its current theory, first look for an
existing owner before introducing a new common/shared theory.  Some generally
useful HOL/library facts may ultimately be better upstreamed or kept temporarily
in an existing `Misc`/props-style theory rather than causing theory proliferation.
