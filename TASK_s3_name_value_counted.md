# TASK: Counted memory simulation for local Name value

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyNameValueMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_name_body_vv_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es ==>
    expr_vv_sim_mem ctx func ce cx ty (Name ann id) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Migrate this one existing root to canonical actual mode-T counted memory execution.
Keep its exact formula, complete posts, all source gas tails, allocation history,
frontier and landing. Preserve the prior successful proof verbatim as a comment.
Build bodyNameValueMemoryTheory and retain its strict kernel gate. No duplicate helpers.
Every other existing public statement and proof must remain unchanged.

## Build

`holbuild -j2 build bodyNameValueMemoryTheory`

The statement is unchanged from its former bodyAllocMemory owner. Its current old
proof has not been built against the counted schema; do not claim it checked.
Independent exact-root static audit classified it PROVABLE unchanged. Common
source/frontier/typed-region owners were built before this job at74b73b0af.

## Background

This producer is required by body memory closure. Counted memory judgments require
an actual target path in mode T and preserve the full relation, history/frontier
and arbitrary gas observations. Existing ordinary mode-F path helpers do not
establish a mode-T path. General forcing and storage-copy producers are separately
owned; do not edit them or assume the desired footprint as a hypothesis.

## Domain Constraints

Only edit lowering/bodyNameValueMemoryScript.sml and its direct imports. Do not change any
shared source/compiler/judgment definition, frozen/public formula, or other proof.
No new axiom/admission, premise, weakened post, subset check, TRY/ORELSE search,
timeout override, force build, cache/checkpoint bypass, holbuild run/repl, or
ordinary-fragment-to-counted-path converse. Reuse canonical source and operational
facts; do not duplicate them or import general forcing through aggregate owners.
If an additional reusable helper is necessary, first search for its canonical owner.

## Available Resources

- lowering/bodyNameMemoryFactsScript.sml: existing typed local region facts.
- lowering/bodyMemoryDefsScript.sml: canonical body local frontier bounds.
- lowering/exprSimSourceScript.sml: source precondition transport, word type facts.
- lowering/exprSimNameWordScript.sml: canonical pure full Name word post.
- lowering/exprSimNameValueScript.sml: canonical raw located Name post/compiler shape.
- lowering/exprSimMemoryValuesScript.sml: complete mode-T value prefix introduction.
- lowering/exprSimMemoryStackScript.sml: canonical raw value/stack adapter.
- lowering/fragGasSeqMemScript.sml: actual counted memory instruction path.
- lowering/fragGasPathMemScript.sml: mode-T path rules.
- lowering/allocaHistoryFragmentScript.sml: instruction history preservation.
- lowering/bodyCalldataMemoryScript.sml and bodyEnvMemoryScript.sml: checked counted leaves.
- lowering/exprSimMemDefsScript.sml, gasNormalPrefixScript.sml and gasSummaryScript.sml: exact full judgments.

## Notes

No generic source-supply or all-oracle storage assumption is authorized. The only
assigned theorem is the frozen root above; final universal body/S3 work is outside
this isolated job. Keep every retained helper/kernel audit; add strict checks for
new helpers used by the root. Keep proof steps/cache/checkpoints enabled.
