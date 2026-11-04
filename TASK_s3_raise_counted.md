# TASK: Counted memory simulation for bare and unreachable raise

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/stmtRaiseMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Prove this counted memory root with no new admission or executable definition.
2. Build stmtRaiseMemoryTheory and pass its strict dependency gate.
3. Preserve the existing successful fixed-result proof as a comment while
   replacing it. Reuse existing helpers rather than duplicating their proofs.

## Build

`holbuild -j2 build stmtRaiseMemoryTheory`

The new statement has not yet been parsed. Its old proof is retained in the
script, referring to private helpers from its former aggregate owner, and is
expected to require replacement. Independent exact-schema audit: PROVABLE.

## Background

This is the memory sibling of the canonical counted stmtSimRaise root. It has
one owner: the old fixed-result declaration was moved from stmtControlMemory,
whose remaining conditional/assert composers still need separate migrations.
This job does not own those composers or the universal body theorem.

## Domain Constraints

No new definitions, axioms, admissions, exclusions, strengthened hypotheses,
timeout overrides or TRY/ORELSE search wrappers. Use default proof steps,
cache and checkpoints. No holbuild run/repl. Keep actual counted mode-T paths,
arbitrary RetQ and all terminal source gas tails. Do not infer a path merely
from conditional frag_exec_mem continuation safety.

Edit only stmtRaiseMemoryScript.sml and required shared helper owners/imports.
Existing ordinary helper statements/proofs may be exported unchanged; preserve
local simp scope. New mode-T siblings belong beside their ordinary helper,
not as duplicated private memory-prefixed proofs. Shared definitions and other
body consumers are read-only. Keep original successful proof code available.
Do not attempt to build or repair the unfinished stmtControlMemory aggregate.

## Available Resources

- lowering/stmtSimRaiseScript.sml: ordinary counted sibling.
- lowering/stmtSimPropsScript.sml: existing emit_abort_zero_path helper.
- lowering/emitHelperPropsScript.sml: canonical abort-step helpers.
- lowering/instMemFrontierScript.sml: instruction frontier checks.
- lowering/fragGasPathMemScript.sml: actual counted memory paths.
- lowering/stmtSimJumpMemScript.sml: counted memory statement examples.
- lowering/stmtSimDefsScript.sml, gasOutcomeScript.sml,
  gasSummaryScript.sml: frozen shared judgment definitions.

## Notes

The other body Alan task is stopped. This independent frozen root has its own
job; do not edit other task state, PLAN or LEARNINGS files.
