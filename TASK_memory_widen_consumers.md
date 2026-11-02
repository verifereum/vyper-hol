# TASK: Layout-converting aggregate assignment statement fragments

## Meta

Theory: stmtSimMemoryWiden. Prove the two new statement fragments below. The recursive typed-copy proof is a separate active task. Its frozen public interface is available in typedMemoryCopyScript.sml; treat it as a prerequisite, do not edit or prove that theory here.

## Theorem Statement (FROZEN)

```sml
Theorem compile_annassign_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' stv dtv.
    eval_stmt cx (AnnAssign id dty e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\ cenv.ce_alloca_locals /\
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

Theorem compile_assign_local_memory_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env ret id dty e es res es' p sz stv dtv.
    eval_stmt cx (Assign (BaseTarget (NameTarget id)) e) es = (res,es') /\
    expr_sim_inv cenv cx env es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME dty /\
    ~is_word_type dty /\ ~(has_length_word dty /\ is_empty_value_expr e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256) /\
    (!v es1 entry.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) /\
       lookup_scopes id es1.scopes = SOME entry ==>
       entry.type = dtv /\ value_has_type stv v /\ value_has_type dtv v) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret (Assign (BaseTarget (NameTarget id)) e)) es res es'


```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

Both named theorems have kernel-checked proofs with no new admissions or axioms. Build only changed/added theories with normal proof checkpoints and default 2.5s step budget. Preserve all existing theorem statements and all executable definitions. Helpers may be introduced only as needed for these consumers; their premises must discharge at the named actual consumers. Do not edit bodySim or its body cases in this task.

## Build

`holbuild -j2 build stmtSimMemoryWidenTheory`

## Background

The existing memory fragments cover equal types and root bytestring widening. Vyper also accepts recursive widening of arrays, tuples and nominal structs containing widened members, including nested bytestring bounds and DynArray capacities. The emitted memory assignment stages its source when the source value is located in memory, then compile_store_memory converts layout as necessary. AnnAssign must support PlaceR through read_result; the older helper requiring every eval_expr result to be Value excludes ordinary names. Tuple assignment is a separate pending prerequisite decision; do not work on it here.

## Domain Constraints

No source/type checker restrictions, no stage/top-level assumptions, and no executable-definition changes. No timeout overrides, TRY/ORELSE search, or full dependent-cone builds. Do not duplicate storage/transient or empty-type work. Root bytestring copies have a specialized actual-length path, so a declared-source-capacity memory bound must not be inferred from an actual footprint. Recursive conversion writes up to the full destination layout.

Independent validation: both statements are PROVABLE by inspection. Tuple widening is deliberately excluded from this task pending a decision on its actual source producer (#767); do not add a supported subset or edit the source checker to bypass that dependency.

## Available Resources

- lowering/stmtSimMemoryWidenScript.sml
- lowering/typedMemoryCopyScript.sml (frozen prerequisite; do not edit)
- lowering/defs/contextScript.sml and typedCopyDomainScript.sml
- lowering/defs/stmtLoweringScript.sml, exprLoweringScript.sml, compileEnvScript.sml
- lowering/stmtSimDeclMemScript.sml, stmtSimAssignMemScript.sml, stmtSimAssignTupleMemScript.sml
- lowering/tupleAssignMemoryScript.sml, tupleLocalStoreRunScript.sml, tupleMemoryFrameScript.sml, tupleStagePropsScript.sml
- lowering/memoryLocalRhsPropsScript.sml, exprSimHypsScript.sml, exprSimScript.sml
- lowering/valueCopyScript.sml, valueCopyBytesScript.sml, valueTypingMemoryPropsScript.sml
- semantics/type/vyperTypeSystemScript.sml and semantics/prop/vyperTypeArgFitsScript.sml

## Notes

The task starts on current origin/main merged into the branch. The core theorem may still be a temporary admission from its independent active proof task; leave it unchanged. Final integration and admission audit are owner work after both tasks finish. Existing admitted leaves outside this scope may be used, but name such dependencies in the result. In particular do not use any existing broad body residual as a proof of these fragments.
