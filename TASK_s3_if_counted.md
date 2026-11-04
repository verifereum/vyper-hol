# TASK: Counted memory composition for conditional statements

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/stmtIfMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_if_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      (eval_stmt cx (If c ss1 ss2)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove the frozen root and build stmtIfMemoryTheory with its strict dependency
gate intact, no new definitions, admissions, hypotheses or weakened posts.
Preserve the prior successful fixed-result proof as a comment while migrating.

## Build

`holbuild -j2 build stmtIfMemoryTheory`

The new statement has not yet been build-parsed. The old proof remains and
refers to private helpers from its former aggregate owner; replace it with the
counted proof while preserving that original code. Independent schema audit
from the source-action migration classified this composition PROVABLE.

## Background

This root is the memory sibling of stmtSimIfCounted.compile_if_stmt_frag, with
exactly its source-action premises and callback. It was moved from the old
stmtControlMemory aggregate; there is only one root declaration. Raise and
Assert have separate jobs/owners. Do not repair the unfinished aggregate here.

## Domain Constraints

Only edit stmtIfMemoryScript.sml and required shared helper exports/imports.
Reuse existing ordinary helpers, exporting unchanged statements/proofs with
their original local simp scope where needed. Do not copy private helpers or
invent renamed duplicates. New mode-T helpers belong beside ordinary siblings.
Shared definitions, other composers and body closure files are read-only.
No stage/program premise, no-GAS exclusion, new axiom/admission, timeout
override or TRY/ORELSE search. Keep default proof steps/cache/checkpoints;
no holbuild run/repl. Actual counted paths must carry memory safety on the
same execution. Retain full posts, original locals/allocas, allocation history,
frontier monotonicity, caller-owned buffer transport and arbitrary RetQ at
every terminal gas tail. Finite storage observations follow the selected source
run; do not add all-oracle storage goodness or transport source traces merely
through gas_obs. Do not change source semantics or executable compiler code.

## Available Resources

- lowering/stmtSimIfCountedScript.sml: canonical counted ordinary root.
- lowering/stmtSimIfPropsScript.sml, stmtSimPropsScript.sml: original helpers.
- lowering/stmtSimSeqMemScript.sml, stmtSimJumpMemScript.sml: memory composers.
- lowering/exprSimMemDefsScript.sml, stmtSimDefsScript.sml,
  bodyMemoryDefsScript.sml: frozen shared judgments and buffer transport.
- lowering/gasSummaryComposeScript.sml, gasOutcomeScript.sml,
  fragGasModeScript.sml, fragGasPathMemScript.sml: counted path toolkit.

## Notes

This is an independent task/worktree. Another job may add a mode-T abort helper
to stmtSimProps on a sibling branch; the owner will reconcile checked results.
Do not edit other tasks' state/PLAN/LEARNINGS files.
