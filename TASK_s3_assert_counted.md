# TASK: Counted memory composition for bare and unreachable assert

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/stmtAssertMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_assert_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      (eval_stmt cx (Assert e ak)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove this root and build stmtAssertMemoryTheory with its strict dependency
gate intact. No new definitions, admissions, premises or weakened posts.
Keep the old successful fixed-result proof available as a comment while
replacing it. Reuse canonical helpers rather than copying their proofs.

## Build

`holbuild -j2 build stmtAssertMemoryTheory`

The new statement has not yet been build-parsed. Its old proof remains,
referring to former private aggregate helpers, and needs counted migration.
Independent exact-schema audit: PROVABLE.

## Background

This is exactly the memory sibling of canonical stmtSimAssert, with the same
source-action premises. The root was moved from stmtControlMemory; only one
declaration remains. Other composers and the universal body have separate
tasks. Do not build or repair the unfinished aggregate.

## Domain Constraints

Edit stmtAssertMemoryScript.sml and required shared helper owners/imports only.
Existing pure source/admissibility/layout/certificate facts must be reused,
exporting unchanged statements/proofs with original local simp scope if needed.
New mode-T helpers belong beside their ordinary sibling. Do not duplicate old
private aggregate helpers. Shared definitions and other body leaves are frozen.
No new stage/program premise, GAS exclusion, axiom/admission, timeout override
or TRY/ORELSE search. Default proof steps/cache/checkpoints; no holbuild run/repl.
Actual counted mode-T paths, complete posts, old locals/allocas, allocation
history/frontier, caller-owned buffer and arbitrary terminal RetQ gas tails
must all remain. A conditional frag_exec_mem witness is not a counted path.
Do not change source semantics, executable lowering or finite-storage policy.

## Available Resources

- lowering/stmtSimAssertScript.sml and stmtSimAssertPropsScript.sml.
- lowering/stmtSimIfPropsScript.sml and stmtSimPropsScript.sml.
- lowering/stmtSimJumpMemScript.sml, stmtSimSeqMemScript.sml.
- lowering/stmtSimDefsScript.sml, exprSimMemDefsScript.sml,
  bodyMemoryDefsScript.sml: canonical frozen judgments and frame transport.
- lowering/gasSummaryComposeScript.sml, gasOutcomeScript.sml,
  fragGasPathMemScript.sml, instMemFrontierScript.sml.

## Notes

Shared stmtSimProps.emit_abort_zero_path_mem and assert_jnz_zero_path_mem
are now joined from the independent Raise/If jobs. Owner check of
stmtSimPropsTheory and stmtRaiseMemoryTheory passed (195.145s), both helper
exports and the Raise kernel audit checked. Reuse these actual mode-T helpers.
