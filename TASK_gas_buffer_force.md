# TASK: Prove counted forcing of a nonword memory buffer

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimBufferForceScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem expr_sim_of_vv_sim_buffer:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa. ?t p sb. compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
      p.ptr_location = LocMemory /\ ~is_word_type t) /\
    (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
    expr_sim ctx func cenv cx ty e es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimBufferForceTheory` passes with the frozen theorem and its retained dependency-integrity gate.
2. No admissions, axioms, parser warnings, timeout overrides, or TRY/ORELSE around search.
3. Preserve all definitions and existing statements. Search before adding helpers; reuse or move existing facts rather than copying them. No let expressions in theorem statements; use explicit record or tuple arguments.

## Build

```sh
holbuild -j2 build exprSimBufferForceTheory
```

## Background

The raw and forced expression judgments now select source observations from counted target execution. This existing buffer-forcing theorem retains its exact statement and original proof, extracted from exprSimUnwrap. Its compiler may allocate and store before returning a nonword memory pointer. Other unwrap forms are outside scope.

## Domain Constraints

An independent audit answered PROVABLE unchanged against the current definitions. Preserve universal admissibility, all unused source tails, actual target execution, readings, full value/allocation/local/memory posts and exact landing. Handle ordinary errors and concrete exemptions with the existing certificate interface. No executable-definition changes, stronger premises, feature restrictions or new certificate constructors. Pure helper owners must not depend on exprSimUnwrap, exprSimCopy or other unported simulation roots.

## Available Resources

- lowering/exprSimBufferForceScript.sml: frozen root and retained proof.
- lowering/exprSimMemorySourceScript.sml: checked admissibility, read-tail and exemption transport facts.
- lowering/exprSimUnwrapPropsScript.sml: shared read-result and full-post facts moved unchanged from exprSimUnwrap.
- lowering/exprSimMemoryForceScript.sml: checked related memory-forcing theorem; its compile state is unchanged, unlike this root.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml: judgments and full posts.
- lowering/gasSummaryComposeScript.sml, lowering/gasSummaryScript.sml, lowering/gasOutcomeScript.sml: counted bind and outcome interfaces.
- lowering/gasExemptCertScript.sml: existing concrete certificate closures.
- lowering/defs/exprLoweringScript.sml, lowering/exprLoweringPropsScript.sml: compiler and structural facts.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source semantics.

## Notes

The independent audit checked normal forcing, raw/forced admissibility, all tails, complete posts, ordinary error transport and existing exemption transport. Preliminary build 65959 built the new owner's dependencies but did not parse the root: its preserved old proof refers to compile_expr_extends, unwrap_value_extends, unwrap_memory_read_result_sim and legacy fragment facts no longer imported. No new imports of the old unported simulation owner should be added to retain those obsolete proof references. No proof strategy is prescribed.
