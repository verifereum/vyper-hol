(* General tuple assignment simulation. *)
Theory stmtSimAssignTupleTargets
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  tupleAssignParts tupleTargetStoreRun tupleTargetStoreProps tupleAssignPrefix
  tupleAssignMemory tupleStageProps tupleLocalStoreProps stmtSimReturn stmtSimAssignTuple 
   exprLowering exprLoweringProps fragExec loweringSlice compileEnv freshWrites
  vyperInterpreter vyperState vyperValue vyperTyping vyperTypeDefaults valueEncoding stmtLowering
  list rich_list finite_map stmtSimDecl stmtSimDeclMem
Libs
  monadsyntax

Theorem stmt_frag_storage_maps_intro:
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
     stmt_frag ctx func cx lctx RetQ cenv m source es) ==>
  stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  cheat
QED

Theorem tuple_target_aligned_sizes:
  !cenv cx g ty tv.
    tuple_target_aligned cenv cx g ty tv ==>
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    0 < type_memory_size tv
Proof
  cheat
QED

Theorem assign_tuple_targets_success_run:
  !ctx func cx lctx cenv ty gs e es es' tys tvs sa sf s0.
    eval_stmt cx (Assign (TupleTarget gs) e) es = (INL (),es') /\
    gs <> [] /\ expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!v es1. (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
    (!vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od) es =
        (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    stmt_env cenv lctx ty (Assign (TupleTarget gs) e) sa = (cenv,sf) /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!fuel r. run_from fuel ctx func t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx func s0 = r)
Proof
  cheat
QED






Theorem compile_assign_tuple_targets_stmt_frag:
  !ctx func cx lctx RetQ cenv ty gs e es tys tvs.
    expr_type e = TupleT tys /\ LENGTH gs = LENGTH tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!obs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := obs) = (INL v,es1) ==>
      value_has_type (TupleTV tvs) v) /\
    (!obs vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od)
        (es with gas_obs := obs) = (INL (ArrayV (TupleV vs)),es1) /\
      i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    gs <> [] /\
    expr_sim ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED


