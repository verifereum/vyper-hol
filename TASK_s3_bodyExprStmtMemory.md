# TASK: Counted body memory composition: body_expr_stmt_mem_case

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyExprStmtMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem body_expr_stmt_mem_case:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Expr e)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove the existing root on the counted source-action memory predicates. Preserve
its old successful proof as a comment when replacing it. Build bodyExprStmtMemoryTheory
with its strict kernel gate intact. No new definitions, admissions, strengthened
premises or weakened posts.

## Build

`holbuild -j2 build bodyExprStmtMemoryTheory`

The existing proof is not checked under this counted schema. Independent audit:
PROVABLE unchanged. Prerequisite source preservation is now independently checked.

## Background

The body predicates quantify over source actions and arbitrary gas tails, and
carry the approved ABI occurrence clause already required by expr_body_pre.
Shared source facts belong to exprSimSource and bodyExprPreFacts; use those
canonical facts rather than reintroducing ordinary statement simulation imports.
Universal body induction and the S3 consumer are separate unfinished work.

## Domain Constraints

Only edit lowering/bodyExprStmtMemoryScript.sml and direct imports. Shared judgments,
source facts and checked composers are read-only. Keep full posts, arbitrary
RetQ, caller return buffers, allocation history/frontier, all source gas tails
and mode-T memory safety. No axiom, cheat, TRY/ORELSE search, timeout override,
checkpoint/cache bypass, force rebuild, holbuild run/repl, ordinary producer
repair or unsupported-subset premise. Don't duplicate existing facts.

## Available Resources

- lowering/bodyExprPreFactsScript.sml and exprSimSourceScript.sml.
- lowering/bodyMemoryPredsScript.sml and bodyMemoryDefsScript.sml.
- lowering/stmtMemoryScript.sml, stmtIfMemoryScript.sml, stmtSimSeqMemScript.sml.
- lowering/exprOpenMainScript.sml: canonical compile_expr_open_general.
- lowering/bodySimScript.sml, gasContextScript.sml, loweringPostsScript.sml.
- lowering/exprSimHypsDefsScript.sml and stmtLoweringMonoScript.sml.
- lowering/supportedStmtTraverseScript.sml and supportedExprTraverseScript.sml.

## Notes

This root must consume the actual checked source-action composers, retaining
terminal/exiting suffix behavior and every permitted gas oracle.
