# TASK: Counted memory simulation for boolean body literals

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyExprMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem body_bool_literal_mem:
  !tops ctx func cenv cx env ty b es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Literal (BaseT BoolT) (BoolL b)) es ==>
    expr_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es /\
    expr_vv_sim_mem ctx func cenv cx ty (Literal (BaseT BoolT) (BoolL b)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Migrate this existing root to canonical counted judgments and build
bodyExprMemoryTheory with its strict kernel dependency gate intact. Preserve
the existing successful proof as a comment while replacing it. No new
definitions, admissions, stronger hypotheses or weakened posts.

## Build

`holbuild -j2 build bodyExprMemoryTheory`

The original proof remains; the statement has not yet been build-parsed under
the current counted join. Independent exact-schema audit: PROVABLE, including
the arbitrary ty quantifier. General ordinary forcing is owned elsewhere.

## Background

The previous root used fixed-result frag_exec_mem. Canonical counted judgments
now require the actual source action and actual mode-T paths. This independent
job owns only the existing boolean-literal conjunction, not general word
literals, other operators, body closure or shared producer migration.

## Domain Constraints

Edit bodyExprMemoryScript.sml and necessary imports only. Shared definitions,
functional proofs and other additive consumers are read-only. Search before
adding helpers; reuse existing canonical facts instead of duplicate renamed
lemmas. Do not import the exprSimHyps/exprSimUnwrap proof cones or general
forcing solely to get definitions: use explicit canonical owners.
No axiom, admission, timeout override, no-GAS/program restriction, new premise
or TRY/ORELSE search. Keep default proof steps, cache and checkpoints; no
holbuild run/repl or redundant force rebuild. Preserve complete posts,
locals/allocas, allocation history/frontier and actual counted paths.
Finite storage observations follow the selected actual source run; no
all-oracle storage premise or transport merely through gas_obs.

## Available Resources

- lowering/exprSimMemDefsScript.sml, exprSimDefsScript.sml: shared contracts.
- lowering/exprSimMemoryValuesScript.sml, exprSimMemoryStackScript.sml:
  canonical counted memory introduction/stack adapters.
- lowering/exprSimHypsDefsScript.sml, bodySimScript.sml, exprSimPropsScript.sml:
  existing body preconditions and post helpers.
- lowering/fragGasModeScript.sml, fragGasPathMemScript.sml,
  gasOutcomeScript.sml, gasSummaryScript.sml: counted path definitions.
- lowering/bodyLiteralMemoryScript.sml: existing broader word family, whose
  old proofs also need migration; do not duplicate or claim them proved here.

## Notes

Other independent composer jobs have completed. The owner is validating their
join in a different worktree. Do not edit other TASK/PLAN/STATE files.
