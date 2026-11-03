# TASK: Prove compile_bop_in_literal_sim

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/exprSimOperatorsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_bop_in_literal_sim:
  !cenv ann bop e1 a t n elems.
    expr_sim_below cenv
      (list_size expr_size [e1; Builtin a (MakeArray t n) elems]) /\
    (bop = In \/ bop = NotIn) ==>
    expr_ok cenv (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Replace the existing admission in `compile_bop_in_literal_sim` with a proof of the exact frozen formula.
2. Build `exprSimOperatorsTheory` at the default step limit. Existing unrelated admissions are allowed dependencies; add no admissions, axioms, definitions or oracle dependencies.
3. Reuse existing theorems. Supporting proof helpers are allowed in their appropriate ancestor; do not duplicate existing or local lemmas. Validate shared helpers before the target.
4. Commit source files only, with trailer `Bot: astra (OpenAI GPT-6 Astra)`. Never commit task files, Alan state, logs, probes or generated artifacts.

## Build

```sh
holbuild -j2 build exprSimOperatorsTheory
```

Keep cache, checkpoints and proof steps enabled. Give the build tool a 3600-second wall limit when needed; never change the per-tactic limit. Build changed helpers by their logical theory names, not the whole dependent cone.

## Background

Prove literal-array membership simulation for both In and NotIn. The source and producer definitions include the primitive-element membership restriction and updated comparison helpers. Keep the expression/body theorem interface unchanged. The separate bytestring equality contract is outside this task.

## Domain Constraints

- Scope: `lowering/exprSimOperatorsScript.sml` and consumed proof helpers in existing appropriate ancestor theories. No executable-definition, checker, semantic, project configuration or other target changes.
- Do not change the frozen formula or strengthen any existing statement. A false formula needs a checked counterexample and handoff.
- Do not use `compile_expr_sim`, `compile_expr_sim_mutual`, `body_sim_mutual`, or a theorem whose admitted dependency includes this target. Do not close this proof through its own admission.
- Preserve all checked negation/power/shift proofs and unrelated admissions. Leave `compile_bop_rest_case` unchanged.
- No search tactic under TRY/ORELSE, no tactic-timeout change, no holbuild run/repl, no Holmake, no interactive g/e/p sessions.
- Use standard quotation style and export reusable proof helpers rather than local copies.

## Available Resources

- `lowering/exprSimOperatorsScript.sml`: frozen target and surrounding simulation patterns.
- `lowering/exprSimHypsScript.sml`: expr_sim_below, expr_ok, expr_sim_case, expr_vv_case and expression preconditions.
- `lowering/bodySimExprCasesScript.sml`: body_expr_ok/body_exprs_ok consumers and literal-array body case.
- `lowering/bodySimScript.sml`: body invariant and judgments.
- `lowering/exprSimAggregatesScript.sml`: aggregate expression simulations.
- `lowering/exprSimAggregateLoopsScript.sml`: array-element loops and tuple reduction.
- `lowering/exprSimAggregateChildrenScript.sml`: aggregate-child judgments and composition.
- `lowering/defs/exprLoweringScript.sml`: compile_multi_exprs, emit_membership_eqs, fold_membership_or, fold_membership_and, literal membership lowering.
- `lowering/exprSimOpsScript.sml`: operator fragments and composition.
- `lowering/exprSimCompareScript.sml`: typed comparison representations.
- `semantics/type/vyperTypeSystemScript.sml`: primitive membership typing and operand checks.
- `semantics/vyperValueOperationScript.sml`: source membership, RHS type and sparse defaults.
- `semantics/vyperInterpreterScript.sml`: evaluation order.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: proof control conventions.

## Notes

The theorem parsed in the previous theory version; the current merged producer baseline has not yet reached this target. Its statement and current definitions received an independent PROVABLE audit. The owner is separately checking the six merge-resolved prerequisite theories. The owner independently audited its statement against the current producer definitions before launch. If an unchanged prerequisite fails, report its exact location; do not broaden scope into unrelated repairs without the owner's instruction. The owner checks final source changes and saved-theorem dependencies after this run.
