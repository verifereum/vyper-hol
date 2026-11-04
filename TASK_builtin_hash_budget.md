# TASK: Repair ci_mono_builtin_hash proof budget

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprLoweringPropsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem ci_mono_builtin_hash[local]:
  (∀ce t e s. ci_mono s (SND (f ce t e s))) ⇒
  ∀bi. (bi = Keccak256 ∨ bi = Sha256) ⇒
  ci_mono st (SND (compile_builtin_dispatch_body f cenv ret_ty ty bi args st))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Repair the existing proof so it builds within the default 2.5-second step limit.
2. Build exprLoweringPropsTheory. Preserve all statements, executable definitions and unrelated proofs; add no admissions or axioms.
3. Commit source files only with trailer `Bot: astra (OpenAI GPT-6 Astra)`. Leave task files, Alan state and generated artifacts out of source commits.

## Build

```sh
holbuild -j2 build exprLoweringPropsTheory
```

Keep cache, checkpoints and proof steps enabled; do not change the tactic limit. A build may use a 3600-second wall allowance.

## Background

The existing ci_mono_builtin_hash proof repeatedly exceeds the default step limit at rpt TOP_CASE_TAC (4043) after splitting the Keccak256 branch. An initial dependent build and one unchanged theory-only retry both failed at this exact step. The frozen theorem must retain its existing meaning and assumptions.

## Domain Constraints

Change only the target proof and consumed proof helpers in its defining theory. Search and reuse existing lemmas before adding anything. Preserve existing target proofs and unrelated admissions. No semantic, checker, project-configuration, statement or definition changes. No search under TRY/ORELSE, no holbuild run/repl, no interactive proof sessions. Do not repair unrelated prerequisite failures without authorization. For a newly encountered untouched step timeout, retry that one theory once unchanged; if the same step repeats, stop and report. Existing ci_mono_builtin_hash retry is exhausted: repair its proof rather than retry unchanged.

## Available Resources

- lowering/exprLoweringPropsScript.sml: target and existing ci_mono composition theorems.
- lowering/defs/exprLoweringScript.sml: compile_builtin_dispatch_body and hashing lowering.
- lowering/defs/contextScript.sml: compiler state definitions, if relevant.
- docs/HOL4_PROOF_CONTROL_LESSONS.md: proof conventions.

## Notes

The formula and existing proof already parse. Preserve every theorem statement byte-for-byte. The owner will check the source diff and build evidence. This task repairs only this encountered prerequisite; it does not prove compile_bop_in_literal_sim.
