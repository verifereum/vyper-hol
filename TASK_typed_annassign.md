# TASK: Typed aggregate memory declaration fragment

## Meta

Status: planned
Created: 2026-11-03
Theory: stmtSimMemoryWiden

## Theorem Statement (FROZEN)

```sml
Theorem compile_annassign_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' stv dtv.
    eval_stmt cx (AnnAssign id dty e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\ cenv.ce_alloca_locals /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type stv v /\ value_has_type dtv v) /\
    (!st0 c st1. declare_local cenv id dty st0 = (c,st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op,sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (AnnAssign id dty e)) es res es'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove the named declaration fragment and its new helpers without admissions or axioms. Preserve its existing partial proof and all existing proven theorem statements. The separately assigned recursive typed-copy theorem is an allowed frozen prerequisite, even while its proof is unfinished; report that dependency explicitly. The unproved Assign fragment is outside this task and may remain unchanged. Do not require an admission-free whole theory while these separate tasks are unfinished.

## Build

`holbuild -j2 build stmtSimMemoryWidenTheory`

Use normal checkpoints and the default 2.5s proof-step budget. A whole build invocation may need timeout 3600 seconds; this does not change the tactic budget.

## Background

The earlier, separate task established a counterexample to the declaration fragment without source expression typing. This task supplies the typing fact already available at its real body caller. Independent inspection of this corrected statement returned PROVABLE, conditional on the frozen typed-copy prerequisite. This is a new task, not a request to resume the false statement.

The declaration fragment covers nonempty memory aggregates, including recursive layout widening and root bytestring widening. It reads source PlaceR results through read_result before adding the declared variable. Its conclusion must describe the actual emitted statement fragment.

## Domain Constraints

No executable-definition changes, source restrictions, new stage assumptions, theorem strengthening, timeout overrides, or TRY/ORELSE around proof search. Do not edit typedMemoryCopyScript.sml, body simulation, or the Assign fragment. Existing inherited admissions outside this task may be used and must be identified; broad admitted body residuals may not prove this fragment. Actual bytestring footprint does not imply a full declared-capacity source-memory bound. Preserve useful proof code from the previous task; diagnostic counterexample and probe material is not a requested deliverable.

## Available Resources

- lowering/stmtSimMemoryWidenScript.sml: existing partial proof, helpers and old annotation counterexample.
- lowering/typedMemoryCopyScript.sml: frozen compile_store_memory_typed_run prerequisite; do not edit.
- lowering/stmtSimDeclMemScript.sml and lowering/stmtSimAssignMemScript.sml: existing declaration and memory fragments.
- lowering/memoryLocalRhsPropsScript.sml: lowered-value type and source annotation relations.
- lowering/exprSimScript.sml and lowering/exprSimHypsScript.sml: expression simulation and placement.
- lowering/valueCopyScript.sml, lowering/valueCopyBytesScript.sml and lowering/valueTypingMemoryPropsScript.sml: copy and footprint facts.
- lowering/typedCopyDomainScript.sml and lowering/defs/contextScript.sml: metadata and layout contracts.
- lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml and lowering/defs/compileEnvScript.sml: actual producer.
- semantics/type/vyperTypeSystemScript.sml and semantics/prop/vyperTypeArgFitsScript.sml: source typing and widening.

## Notes

The typing premise is newly added to an unproved internal fragment. The corrected statement has not yet been parse-built in this run; the prior statement and preserved partial proof were built before the correction. Owner validation, CI-mode replay and final admission audit follow this task. The old memory_widen_consumers task and its frozen statement remain as historical evidence; do not edit or resume its verified-falsehood state.
