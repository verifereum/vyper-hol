# TASK: Repair membership-loop operand safety proof budget

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSafeOperandBuiltinsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_array_membership_loop_safe_operand:
  (!p s v t. loader p s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
  compile_array_membership_loop needle arr len sz off loader bound isin sa = (r,sb) ==>
  safe_operand sb r
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Repair the existing proof to pass the default 2.5-second step limit.
2. Build exprSafeOperandBuiltinsTheory; retain all existing statements, definitions and unrelated proofs. Add no admissions or axioms.
3. Commit source files only, with trailer `Bot: astra (OpenAI GPT-6 Astra)`.

## Build

```sh
holbuild -j2 build exprSafeOperandBuiltinsTheory
```

Keep cache, checkpoints and proof steps enabled. A 3600-second wall allowance is permitted; no tactic-limit change.

## Background

The target's repeated pairarg simplification exceeded the step limit in the baseline build and one isolated unchanged retry. Its statement already parses. The current compiler includes the optional bound parameter; older repairs from before that parameter cannot replace its statement or definition.

## Domain Constraints

Change only this proof and directly consumed proof helpers. Search existing lemmas before introducing any; reuse or export existing results instead of duplicating them. No semantic, checker, configuration or statement changes. No search wrapped in TRY/ORELSE. No holbuild run/repl or interactive sessions. Preserve existing proofs, and do not repair unrelated prerequisite failures. For a newly encountered untouched timeout, retry that one theory once unchanged; stop and report if the same step repeats. The target's retry is already exhausted.

## Available Resources

- lowering/exprSafeOperandBuiltinsScript.sml: target, safe-operand and counter-monotonicity lemmas.
- lowering/exprLoweringPropsScript.sml: existing compiler monotonicity results.
- lowering/defs/exprLoweringScript.sml: membership-loop producer including bound parameter.
- lowering/exprSafeOperandScript.sml: search for shared operand-safety facts.
- docs/HOL4_PROOF_CONTROL_LESSONS.md: proof conventions.

## Notes

This is a prerequisite repair only. Do not modify compile_bop_in_literal_sim or other task files. The owner will inspect the source diff and build evidence.
