(* Layout-converting stores into memory locals, after expression evaluation. *)
Theory stmtSimMemoryWiden
Ancestors
  list finite_map exprSim exprSimHyps stmtSim stmtSimDeclMem
  stmtSimAssignMem stmtSimAssignTupleMem typedMemoryCopy
  stmtLowering exprLowering compileEnv valueEncoding vyperTypeSystem
  vyperInterpreter vyperState
Libs
  monadsyntax

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
Proof
  cheat
QED

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
Proof
  cheat
QED

Theorem compile_assign_tuple_locals_typed_stmt_frag:
  !ctx func cx lctx RetQ cenv env env' ret ids e es res es' tys tvs.
    eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
      es = (res,es') /\
    expr_sim_inv cenv cx env es /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_stmt env ret (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
      SOME env' /\
    ids <> [] /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==>
       cenv.ce_target CapMcopy /\ type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH ids ==>
       ?p sz dty dtv.
         FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME dty /\
         type_widens_to (get_tenv cx) (EL i tys) dty /\
         evaluate_type (get_tenv cx) dty = SOME dtv /\
         type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
         type_memory_bytes cenv dty = type_memory_size dtv /\
         0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256)) /\
    (!v es1.
       (do raw <- eval_expr cx e; read_result cx raw od) es = (INL v,es1) ==>
       value_has_type (TupleTV tvs) v) /\
    (!vs es1 i entry.
       (do raw <- eval_expr cx e; read_result cx raw od) es =
         (INL (ArrayV (TupleV vs)),es1) /\
       i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) entry.type (EL i vs)
       else
         ?dty. cenv.ce_var_type (EL i ids) = SOME dty /\
               evaluate_type (get_tenv cx) dty = SOME entry.type /\
               value_has_type entry.type (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es res es'
Proof
  cheat
QED
