# TASK: Prove counted simulation of bytes and string literal buffers

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimLiteralBufferScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_literal_other_vv_sim:
  !cenv ann l.
    ((?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)) ==>
    expr_vv_ok cenv (Literal ann l)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimLiteralBufferTheory` passes with the frozen root and existing dependency-integrity gate.
2. No admissions, axioms, parser warnings, timeout overrides, or TRY/ORELSE around search.
3. Preserve every definition and existing theorem statement. Search before adding helpers; reuse or move matching existing facts rather than duplicating them. No let expressions in theorem statements.

## Build

```sh
holbuild -j2 build exprSimLiteralBufferTheory
```

## Background

The raw expression judgment now relates source gas observations to actual counted target execution. This existing theorem retains its exact statement and original proof. Literal buffers allocate memory, store their length and padded byte chunks, and return a memory pointer. Existing pure execution and frame facts remain in the same owner. Unrelated expression simulation roots are outside scope.

## Domain Constraints

An independent definition/producer audit answered PROVABLE unchanged, including empty buffers, partial chunks, allocation reuse and constructor immutables. Preserve universal admissibility, every unused source tail, actual instruction execution/count, target readings, full value and allocation provenance, locals and memory frames, and the exact landing. No executable-definition changes, stronger premises, feature restrictions, new exemptions or certificate constructors. Pure prerequisites must not import unported exprSimOps, exprSimWordArgs, exprSimHyps or exprSimUnwrap roots.

## Available Resources

- lowering/exprSimLiteralBufferScript.sml: existing root, retained proof, actual instruction-run and frame facts.
- lowering/fragGasSeqScript.sml: generic counted straight-line bridge moved unchanged from stmtSimReturnTuple.
- lowering/exprSimPropsScript.sml: existing local-region frame facts moved unchanged from exprSimOps.
- lowering/loweringPostsScript.sml: existing wb_frame definition moved unchanged from exprSimWordArgs, plus full posts.
- lowering/exprSimLiteralWordScript.sml: existing source literal evaluation facts.
- lowering/exprSimAllocScript.sml: allocation and immutable framing facts.
- lowering/exprSimHypsDefsScript.sml, lowering/exprSimDefsScript.sml: preconditions and raw counted simulation.
- lowering/gasSummaryScript.sml, lowering/gasSummaryComposeScript.sml, lowering/gasOutcomeScript.sml: counted summary interfaces.
- lowering/defs/exprLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual literal compiler.
- lowering/defs/valueEncodingScript.sml, lowering/proofs/valueEncodingProofsScript.sml: memory layout.
- semantics/vyperInterpreterScript.sml, semantics/vyperValueOperationScript.sml: actual source literal evaluation.

## Notes

An independent audit checked the actual source/compiler producers, all gas tails, allocation and initialized-immutable frames, local/older-allocation memory preservation and full vv_post. Preliminary build 65918 is still running; the root has not yet been parsed under the trimmed independent imports. The moved loweringPosts and fragGasSeq prerequisites have built. No proof strategy is prescribed.
