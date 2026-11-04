# TASK: Repair the explicit endpoint form of counted memory forcing

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimMemoryReadScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem unwrap_memory_marked_read:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimMemoryPathTheory exprSimMemoryReadTheory exprSimMemoryForceTheory` passes.
2. Preserve this exact root, every existing statement and all definitions. The no-let endpoint helper must keep its existing logical content.
3. Keep the memory-force dependency-integrity gate passing. No admissions, axioms, timeout overrides, parser warnings or TRY/ORELSE around search.
4. No let expressions in theorem statements. Reuse existing source, compiler, full-post and counted path facts rather than duplicating them.

## Build

```sh
holbuild -j2 build exprSimMemoryPathTheory exprSimMemoryReadTheory exprSimMemoryForceTheory
```

## Background

The counted memory-forcing theorem and this intermediate read theorem passed the original Alan run. Its new emit_mload_endpoint helper used a let expression in its statement. That helper now expresses the same concrete record endpoint directly and builds, but the existing consumer proof no longer recovers the abbreviated endpoint facts. Repair that proof while preserving the statements and all complete posts.

## Domain Constraints

Preserve actual zero-GAS MLOAD or no-instruction memory forcing, every unused source tail, target readings, exact cursor, full value/allocation/local/memory posts and existing concrete exception transport. No feature restrictions, new hypotheses or certificates. Other expression roots are outside scope.

## Available Resources

- lowering/exprSimMemoryReadScript.sml: frozen theorem and existing proof.
- lowering/exprSimMemoryPathScript.sml: actual MLOAD/compiler boundaries and no-let endpoint helper.
- lowering/exprSimMemorySourceScript.sml: source admissibility/read-tail/exemption boundaries.
- lowering/exprSimUnwrapPropsScript.sml: existing complete post transport.
- lowering/exprSimMemoryForceScript.sml: frozen final consumer and its dependency-integrity gate.
- lowering/exprSimPropsScript.sml, lowering/loweringPostsScript.sml: shared frames and posts.
- lowering/emitHelperPropsScript.sml, lowering/fragGasPathScript.sml, lowering/gasSummaryScript.sml: actual execution boundaries.

## Notes

Build 66139 parsed the unchanged read theorem and reached its MLOAD post proof. The helper builds; the consumer fails while connecting its concrete endpoint operand fact to the locally abbreviated state. The original memory-forcing root statement remains byte-identical to 869e02ba4. A fresh independent audit of this exact read statement answered PROVABLE unchanged, with no semantic premise gap. No proof strategy is prescribed.
