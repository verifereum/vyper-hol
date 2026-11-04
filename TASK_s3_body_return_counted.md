# TASK: Counted body memory composition for Return with a value

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyReturnMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem body_return_mem_ok:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Return (SOME e))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove the existing root using the current counted body memory predicates and
full frame return contract. Preserve the old successful proof as a comment.
Build bodyReturnMemoryTheory with its strict kernel gate intact. No definition,
admission, strengthened hypothesis or weakened post.

## Build

`holbuild -j2 build bodyReturnMemoryTheory`

The existing proof has not been built on this counted join. Independent audit:
PROVABLE after the approved ABI coverage propagation. Universal body induction
is a separate unfinished task.

## Background

body_stmt_mem_ok and body_stmts_mem_ok now carry the exact ABI-target occurrence
coverage already in their ordinary siblings. Actual FunctionDecl body membership
supplies coverage at S3 entry, without a new top-level premise. body_inv supplies
dynamic ABI-type compatibility and module lookup. The existing common source
owner bodyExprPreFacts has been reused, with no duplicate facts; its corrected
stmt_expr_body_pre carries the two corresponding canonical expression clauses.
The common source owner passed its focused build and five strict audits.

## Domain Constraints

Only edit bodyReturnMemoryScript.sml and its direct imports. Shared definitions,
bodyExprPreFacts and the checked base predicates are read-only. Do not duplicate
their helpers. Keep the complete counted mode-T judgment, caller return buffer,
allocation history/frontier and arbitrary RetQ/source gas tails. No axiom,
admission, TRY/ORELSE search, timeout override, holbuild run/repl, checkpoint/cache
bypass or force rebuild. Do not repair ordinary statement producers.

## Available Resources

- lowering/bodyMemoryPredsScript.sml and bodyMemoryDefsScript.sml.
- lowering/bodyExprPreFactsScript.sml: corrected shared source boundary.
- lowering/bodySimScript.sml and gasContextScript.sml.
- lowering/exprSimHypsDefsScript.sml.
- lowering/supported/supportedProgramScript.sml and supportedStmtTraverseScript.sml.

## Notes

This root composes the existing return contract; the contract's concrete return
execution producers remain independently owned. Do not weaken it to a
fixed-result continuation or omit terminal gas suffixes.
