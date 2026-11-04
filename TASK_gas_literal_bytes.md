# TASK: Prove counted address and fixed-byte literal simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimLiteralBytesScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_literal_bytes_word_sim:
  !ctx func cenv cx env ty ann bs es.
    expr_sim_pre cenv cx env (Literal ann (BytesL bs)) es /\
    is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann (BytesL bs)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimLiteralBytesTheory` passes with the frozen root.
2. No admissions, axioms, parser warnings, timeout overrides, or TRY/ORELSE around search.
3. Preserve every definition and existing theorem statement. Search before adding helpers; reuse or export existing matching facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimLiteralBytesTheory
```

## Background

The expression judgment now relates source observations to the counted target prefix. This existing address/bytesN literal theorem retains its exact statement and original proof. It and its exclusive ML helper have been extracted from exprSimLeaves into an independent owner. Other literal roots and wrappers are outside this task.

## Domain Constraints

An independent audit answered PROVABLE for this exact statement against current definitions, including bytes0 and address alignment. Preserve universal source admissibility, every unused source tail, actual counted execution, target readings and the full expression postcondition. No executable-definition or theorem-premise changes, feature restrictions, new exemptions or certificate constructors. Shared facts belong in an appropriate common ancestor; do not duplicate them.

## Available Resources

- lowering/exprSimLiteralBytesScript.sml: frozen root and retained proof.
- lowering/exprSimLiteralWordScript.sml: existing generic literal source-evaluation facts.
- lowering/exprSimValuesScript.sml, lowering/gasNormalPrefixScript.sml: counted normal-value interface.
- lowering/exprSimHypsDefsScript.sml, lowering/exprSimPropsScript.sml: preconditions and shared source/frame facts.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml: shared judgment and full postcondition.
- lowering/fragGasPathScript.sml, lowering/gasSummaryScript.sml: counted target paths.
- lowering/defs/exprLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual compiler.
- lowering/defs/valueEncodingScript.sml, lowering/proofs/valueEncodingProofsScript.sml: typed word encoding.
- semantics/vyperInterpreterScript.sml, semantics/vyperValueOperationScript.sml: source evaluation.

## Notes

Preliminary build 65542 parsed the exact statement and reached its original proof, which failed because it still concludes the old fragment execution judgment. Ancestors built successfully. The audit checked the well-typed AddressT and BytesT (Fixed m) cases, source evaluation for every gas tail, exact compiler encoding and the complete postcondition. No proof strategy is prescribed.
