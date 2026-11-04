# TASK: Prove finite storage observation mask properties

## Meta
- Scope: lowering/accountsRelPropsScript.sml and this task file only.
- The owner has threaded H=(regions,locks) through the compiler state/account,
  transient, request and result relations in compileEnv. Other compiler files
  are owner work. Source property proofs and evaluator erasure are separate runs.
- Do not edit any definitions or any pre-existing theorem statement.

## Theorem Statement (FROZEN)
All existing theorem statements in accountsRelProps are frozen as currently
written. The six finite mask properties in particular are:
```sml
Theorem observed_storage_region_read_live:
  !H cx tr w tv st.
    MEM (tr,w,tv) (FST H) ==>
    storage_read_live H cx tr st w tv

Theorem storage_agree_storage_dead_on:
  !cx tr st1 st2.
    storage_agree (storage_dead_on H tr st1) st1 st2 ==>
    storage_dead_on H tr st2 = storage_dead_on H tr st1

Theorem storage_dead_on_update_in_region:
  !H tr k0 tv0 k u st.
    MEM (tr,k0,tv0) (FST H) /\
    (w2n k0 + type_slot_size tv0 <= dimword (:256) ==>
     w2n k0 <= w2n k /\ w2n k < w2n k0 + type_slot_size tv0 /\
     !j b. dead_bytes (update_storage k u st) (w2n k0) tv0 j b <=>
           dead_bytes st (w2n k0) tv0 j b) ==>
    storage_dead_on H tr (update_storage k u st) = storage_dead_on H tr st

Theorem storage_dead_on_update_word_region:
  !H tr k tv v st.
    MEM (tr,k,tv) (FST H) /\
    type_slot_size tv = 1 ==>
    storage_dead_on H tr (update_storage k v st) = storage_dead_on H tr st

Theorem storage_dead_on_update_struct_word_field:
  !H tr k fs fld off ftv u st.
    MEM (tr,k,StructTV fs) (FST H) /\
    struct_field_slot fs fld = SOME (off, ftv) /\ type_slot_size ftv = 1 ==>
    storage_dead_on H tr (update_storage (k + n2w off) u st) =
    storage_dead_on H tr st

Theorem storage_dead_on_update_zero:
  !cx tr st k j b.
    storage_dead_on H tr st j b ==>
    storage_dead_on H tr (update_storage k 0w st) j b
```
Do not modify this statement. Prove it as-is, or produce a counterexample.
This applies to every existing statement in the scoped file, not only these six.

## Completion Criteria
- Repair proofs and build accountsRelPropsTheory with no new assumptions.
- Keep every existing substantive result, including the original global
  storage_dead_* and storage_agree_storage_dead results retained at the end.
- Search for and reuse existing facts before adding helpers. Do not duplicate
  existing lemmas or add unused theorem families.
- Commit only the permitted source file and task file; never push. End each
  commit with Bot: sol (OpenAI GPT-6.1 Sol).

## Build
`holbuild -j4 build accountsRelPropsTheory`
These statements have received an independent read-only audit: PROVABLE. They
have not all parsed in a build: source ancestors are undergoing the same ghost
trace migration, separately owned. An owner build of compileEnv reached
vyperLookupStorageScopes.lookup_global_scopes_fst; its owner is repairing it.
If an out-of-scope ancestor still fails, report it without editing it.

## Background
storage_dead_on H replaces declared-path quantification by a finite list of
physical (backend,slot,type) roots, and keeps every observed transient lock word
live. Same physical typed roots may alias; other mask witnesses must frame each
other. ranges_disjoint already includes BOTH ranges fitting the slot space.
The active compiler relations use this finite mask. The original declared-mask
results remain independently meaningful and are retained under their old names.
Existing proof bodies are preserved starting attempts and still contain obsolete
logical-path witness variables in the finite counterparts.

## Domain Constraints
- Default 2.5s tactic timeout. No override/bypass, no TRY/ORELSE around search.
- No new admission, axiom, cheat, definition change, dropped result or stronger
  hypothesis. An actual H member replaces a declared path at finite read/write
  boundaries; no global keccak/layout assumption is allowed.
- Never invoke run/repl/Holmake or the full CI/bytecode rollup.
- Source and compiler owner edits outside accountsRelProps remain untouched.

## Available Resources
- lowering/defs/compileEnvScript.sml: storage_dead_on, storage_read_live,
  storage_agree, and horizon-parametric account/transient/request/state relations.
- lowering/accountsRelPropsScript.sml: existing generic storage_agree and
  dead_bytes frame properties, and retained global mask properties.
- semantics/prop/vyperStorageFrameScript.sml: ranges_disjoint with no-wrap bounds.
- semantics/vyperStateScript.sml and semantics/vyperCallOutcomeScript.sml:
  ghost logging, actual oracle take/adopt records.
- semantics/prop/vyperCallOutcomeFrameScript.sml: checked monadic frame kit.

## Notes
H is internal. The public end-to-end predicates derive it from exactly the source
execution they compare. This task is the finite byte-mask layer, not whole-call
correctness or oracle-off/delegate equivalence.
