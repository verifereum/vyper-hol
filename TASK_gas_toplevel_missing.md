# TASK: Prove counted top-level name simulation for missing

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimTopLevelMissingScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_toplevel_no_module_sim:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimTopLevelMissingTheory` passes with the unchanged frozen root.
2. Add an inline theorem-tag check requiring no axioms, no hypotheses and only DISK_THM oracles for the root.
3. Preserve all existing definitions and theorem statements. Add no admissions, parser warnings, timeout overrides or TRY/ORELSE around search.

## Build

```sh
holbuild -j2 build exprSimTopLevelMissingTheory
```

## Background

The shared raw-expression judgment now carries actual counted target execution and uniform source gas tails. This existing leaf theorem retains its exact statement and old proof. It was extracted from exprSimLeaves into an independent owner so unrelated unfinished leaves do not block it. The shared pure prerequisites are extracted without changing their statements or proofs. The first pure-prerequisite build failed at a missing direct vyperTypeValues import; the import is repaired and a retry is running. This root has not yet been parsed under the new imports.

## Domain Constraints

An independent audit checked actual source, lowering and judgment definitions and answered PROVABLE for this exact statement. Keep all-tail source admissibility, complete raw vv_post, target landing, all old variable/allocation/local memory frames and exact pointer provenance. No executable-definition changes, stronger hypotheses, new exemption constructors, restricted feature coverage or stage assumptions. Search before adding helpers: reuse/export/move existing matching facts. Do not import exprSimLeaves, exprSimOps, exprSimUnwrap or other unported simulation roots. Other top-level roots have independent jobs; do not change their files. No let in theorem statements.

## Available Resources

- lowering/exprSimTopLevelMissingScript.sml: exact frozen root and retained old proof.
- lowering/exprSimTopLevelPropsScript.sml: existing pure lookup, storage decoding and layout facts moved unchanged.
- lowering/exprSimNameValueScript.sml: checked counted raw local-name leaf and source/frame properties.
- lowering/exprSimMemorySourceScript.sml: existing successful read_result gas-tail transport.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml, lowering/exprSimHypsDefsScript.sml: actual counted judgment, full posts and source/compiler invariant.
- lowering/exprLoweringPropsScript.sml, lowering/defs/exprLoweringScript.sml: compiler facts and definition.
- lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/fragGasPathScript.sml: counted execution interface.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source lookup and immutable/storage reads.
- semantics/prop/vyperTypeInvariantsScript.sml, semantics/prop/vyperStorageLayoutSafetyScript.sml: source typing and storage validity.

## Notes

The existing old proof is retained verbatim. It targets the previous uncounted interface and is expected to need migration. Preserve useful existing helpers. The inline check and ordinary owner build provide completion evidence; no external scratch build or unavailable shell tool is a completion criterion.
