# TASK: Counted memory value simulation for word body literals

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyLiteralMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_literal_word_body_vv_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_vv_sim_mem ctx func cenv cx ty (Literal ann l) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove the existing root under canonical counted memory judgments and build
bodyLiteralMemoryTheory with its strict kernel gate intact. Preserve its old
successful proof as a comment while replacing it. No new definitions,
admissions, strengthened assumptions or weakened posts.

## Build

`holbuild -j2 build bodyLiteralMemoryTheory`

The original proof remains and has not yet been built under this counted
join. Independent exact-schema audit: PROVABLE, including arbitrary ty.

## Background

This independent job owns the raw value root. The existing forced root and its
private tactic moved unchanged to bodyLiteralForceMemory for a separate later
job; do not repair or build it here. Consumers now import its new owner, but
their own migrations are separate and not claimed checked.

To avoid the unfinished exprSimLeaves proof cone, its existing
compile_literal_bytes_stack theorem moved unchanged to exprLoweringProps;
the old declaration was removed, not copied. exprSimLeaves already imports
that owner. Keep that exact statement/proof intact. The body literal ancestor
list now names canonical definition/helper owners instead of general forcing.

## Domain Constraints

Edit bodyLiteralMemoryScript.sml and required imports only. The moved compiler
fact is frozen as-is; functional source proofs and executable definitions are
read-only. Existing body_literal_word_compile may be exported unchanged with
local simp scope retained if another actual consumer needs it. No duplicates.
No stronger premise, axiom/admission, timeout override or TRY/ORELSE search.
Keep default proof steps/cache/checkpoints; no holbuild run/repl or redundant
force rebuild. Actual counted mode-T paths must retain complete posts,
locals/allocas, allocation history/frontier and all source gas tails.
Do not introduce all-oracle storage goodness or transport merely via gas_obs.
Do not edit bodyLiteralForceMemory or other body consumers beyond imports.

## Available Resources

- lowering/exprSimMemDefsScript.sml, exprSimHypsDefsScript.sml,
  exprSimPropsScript.sml: canonical contracts and existing post helpers.
- lowering/exprSimMemoryValuesScript.sml, exprSimMemoryStackScript.sml:
  existing counted memory adapters.
- lowering/exprLoweringPropsScript.sml: original compiler literal fact.
- lowering/exprSimLiteralWordScript.sml: ordinary counted source helper;
  its mode-F prefix alone does not establish mode-T memory execution.
- lowering/fragGasPathMemScript.sml, fragGasModeScript.sml,
  gasOutcomeScript.sml, gasSummaryScript.sml.

## Notes

Boolean-only bodyExprMemory has a separate active job in another worktree;
do not modify it here. This job does not own universal body coverage.
