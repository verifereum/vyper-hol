# TASK: Prove counted forcing of a compiled memory value

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimMemoryForceScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem expr_sim_of_vv_sim_memory:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv, sm) ==>
                sm = sa /\
                ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory) ==>
    expr_sim ctx func cenv cx ty e es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimUnwrapPropsTheory exprSimMemoryForceTheory` passes with the assigned root and its integrity gate.
2. No admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. Preserve all definitions and existing theorem statements. Search before adding helpers; export or move matching existing facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimUnwrapPropsTheory exprSimMemoryForceTheory
```

## Background

The existing theorem is unchanged, with its old proof retained. Shared raw/forced expression judgments now use actual source actions under selected explicit gas observations. The raw compiler fragment is empty and produces a value located in memory; forcing adds the real unwrap fragment. Four existing pure post/read facts moved unchanged from exprSimUnwrap to exprSimUnwrapProps so this root does not depend on the unported general unwrap/copy roots.

## Domain Constraints

An independent exact statement audit answered PROVABLE, including universal admissibility, all unused source tails, ordinary/error paths and concrete exemption transport. Preserve the full expression postcondition, target cursor, local and allocation frames. Uncounted frag_exec alone cannot supply a counted target suffix. Add no theorem premise, executable definition, evaluator, feature restriction, arbitrary source-equivalence certificate or new exemption. Existing certificate constructors suffice. The general unwrap/copy roots and other expression leaves are outside scope.

## Available Resources

- lowering/exprSimMemoryForceScript.sml: exact root, retained proof and integrity gate.
- lowering/exprSimUnwrapPropsScript.sml: four existing pure read/post/exception transport facts.
- lowering/exprSimPropsScript.sml, lowering/exprLoweringPropsScript.sml: state relations and compiler-growth facts.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml: counted judgments and full posts.
- lowering/gasSummaryComposeScript.sml, lowering/gasOutcomeScript.sml, lowering/gasExemptCertScript.sml: actual source-action composition and existing concrete exemption transports.
- lowering/emitHelperPropsScript.sml, lowering/fragGasPathScript.sml: actual instruction paths.
- lowering/freshWritesScript.sml: variable and allocation frame monotonicity.
- lowering/defs/exprLoweringScript.sml: actual unwrap_value compiler.
- semantics/vyperStateScript.sml: read_result and source-state operations.

## Notes

Preliminary build 64236 checked exprSimUnwrapPropsTheory, then stopped on ML references to unwrap_value_extends and unwrap_memory_read_result_sim in the retained obsolete root proof. The new root has not yet been parsed; the independent exact statement audit is its current statement check. All four moved theorem bodies remain unchanged. Do not import exprSimUnwrap or exprSimCopy to regain their obsolete uncounted roots. No proof strategy is prescribed.
