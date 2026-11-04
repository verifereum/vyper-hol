# TASK: Canonical source-action equality for recursive unary builtins

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/exprSimUnopPropsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem eval_expr_unop_action:
  (bi = Not \/ bi = Abs \/ bi = Neg) ==>
  (bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. (unop_result cx ann bi [expr_type e] v es, es)))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove this single canonical source-action equality and remove its temporary
admission. Build exprSimUnopPropsTheory with its new strict kernel gate passing,
all sixteen pre-existing public property statements/proofs unchanged, and strict
gates for any new helper consumed by this root. No new admission may remain.

## Build

`holbuild -j2 build exprSimUnopPropsTheory`

The statement has an independent exact PROVABLE audit against evaluate_def,
read_result, bind/get_accounts/lift_sum and unop_result. Preflight builds the new
statement under a temporary admission solely for parsing; its strict gate rejects
that admission, so no proof release is claimed until this task proves it.

## Background

The recursive Not/Abs/Neg counted memory consumers need a source-action equality
for canonical source-indexed exception certificates. The existing one-direction
fixed-result eval_expr_unop_cases is insufficient as function equality. This
shared owner serves the three actual recursive builtins, preserving child state
and account changes, source gas tails and all error outcomes. The existing
expr_body_pre_gas_admissible has been moved unchanged to exprSimSource separately;
this task need not invent an unrestricted parent-to-child admissibility lemma.

## Domain Constraints

Only edit lowering/exprSimUnopPropsScript.sml and its direct imports. All existing
public statements, proofs and definitions stay unchanged. No new definitions,
compiler/source executable changes, new assumptions or stage amendments, weakened
statement, axiom/admission, TRY/ORELSE search, raised timeout, forced rebuild,
checkpoint/cache bypass, or holbuild run/repl. The temporary new-root admission
must disappear rather than be retained as a misleading old successful proof.
Search existing source facts before adding a helper; no duplicate lemma family.

## Available Resources

- lowering/exprSimUnopPropsScript.sml: unop_result and eval_expr_unop_cases.
- lowering/exprSimSourceScript.sml: canonical source preconditions and evaluation facts.
- semantics/vyperInterpreterScript.sml: evaluate_def, especially Builtin and eval_exprs equations.
- semantics/vyperStateScript.sml: bind, read_result, get_accounts, lift_sum and state/error constructors.
- semantics/vyperContextScript.sml: builtin_args_length_ok and evaluate_builtin.
- lowering/exprLoweringPropsScript.sml: eval_expr_builtin_value.

## Notes

Malformed annotations/values and child evaluation/read errors are covered by the
frozen equality; do not add typing or child-success premises. Every post-child
account/state effect must be retained. No canonical judgment is changed.
