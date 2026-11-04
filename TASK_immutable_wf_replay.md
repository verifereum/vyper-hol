# TASK: Bound the immutable admissibility well-formedness proof

## Meta
Status: planned; independent truth audit PROVABLE
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem immutable_admissible_val_wf:
  (!tv v. immutable_value_admissible tv v ==> val_wf tv v) /\
  (!vs tvs. immutable_fields_admissible tvs vs ==> fields_val_wf vs tvs) /\
  (!vs tv. EVERY (immutable_value_admissible tv) vs ==> elems_val_wf vs tv) /\
  (!kvs tv n.
     EVERY (\(k,v). k < n /\ immutable_value_admissible tv v) kvs ==>
     kvs_val_wf kvs tv n) /\
  (!vs tvs. immutable_tuple_admissible tvs vs ==> tuple_val_wf vs tvs)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

All existing schemas, definitions, ML tactics, other proof bodies and files
are frozen at 5ebd10672. Change only this root's proof and necessary consumed
local helpers in lowering/loweringSliceScript.sml. Retain its existing proof
until replacing it. This task covers one coupled theorem, not other
immutable-memory or lowering roots.

## Completion Criteria

1. The complete unchanged root builds at the default step limit without new
   admissions or CHEAT warnings.
2. All other schemas, definitions, proof bodies, ML tactics and files stay unchanged.
3. Report the named-target result and any later failure without expanding scope.
   The owner performs one cached default checkpoint-free check after return.

## Build

```sh
holbuild -j4 build loweringSliceTheory
```

## Background

A focused downstream build and its one permitted unchanged-theory rerun
both stopped in this existing proof at a simplifier applied to 192 constructor
goals. The complete statement parses. Admissibility, footprint well-formedness,
capacity rounding and existing memory relations must retain their definitions.
No canonical-padding requirement or stronger premise may be introduced.

## Domain Constraints

- Preserve the complete frozen schema and every other existing theorem proof.
- No new cheat, axiom, hypothesis, restricted subset or opaque fact.
- Default 2.5s limit; never raise it, disable checks or catch timeouts.
- No new TRY/ORELSE/FIRST around search; select goals explicitly.
- Use holbuild only; no interactive HOL, Holmake, run/repl or explicit theory loads.
- Reuse existing facts before adding necessary consumed local helpers.
- Report later failures without expanding scope or resuming a completed task.
- Commit only substantive source edits; leave Alan working files untracked.
  End commits with `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/loweringSliceScript.sml`: frozen root and its immutable-memory consumers.
- `lowering/defs/immutableEncodingScript.sml`: complete admissibility family.
- `lowering/proofs/immutableEncodingProofsScript.sml`: existing admissibility and capacity facts.
- `lowering/defs/valueEncodingScript.sml`: val_wf and its mutually recursive families.
- `lowering/valueEncodingPropsScript.sml`: existing encoding and footprint facts.
- `semantics/vyperValueScript.sml`: source values.
- `syntax/vyperASTScript.sml`: all source types and bounds.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: proof-control conventions.

## Notes

Independent source audit found the complete conjunction PROVABLE across all
type/value constructors, bounds, empty lists, zero capacities and sparse-array
duplicates. This is a truth audit, not a kernel proof.

The owner compares all frozen schemas and every byte outside the permitted
proof/helper area. The downstream gas-oracle call check remains unfinished.
