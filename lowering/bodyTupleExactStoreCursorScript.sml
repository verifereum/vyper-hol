(* State at the start of the remaining exact-layout tuple stores.
 * This carries neither child simulation hypotheses nor source admissibility. *)
Theory bodyTupleExactStoreCursor
Ancestors
  exprSimHypsDefs[qualified]
  bodyFullPreds targetPlaceSim supportedStmts vyperTypeSystem vyperTypeDefaults
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperStorageFootprint
  stmtLowering gasShadow gasShadowState stmtSimDefs loweringPosts
  loweringStateRelDefs exprLoweringProps fragExec contextRawReachable
  ptrDiscipline unitTransformDefs allocaHistory bodyPtrDefs valueEncoding
  valueEncodingDefs vyperTypeValues list finite_map words

Definition tuple_exact_cursor_common_def:
  tuple_exact_cursor_common (cenv,cx,env,tops,bindings)
    (lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
    (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
    (cur,shadow_cur,src,u,Gu,tu) <=>
    LIST_REL (\g ty. well_typed_atarget env g ty) todo tys1 /\
    LENGTH ops1 = LENGTH tys1 /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys1 tvs1 /\
    values_have_types tvs1 vs1 /\ tys1 = DROP k tys /\
    tvs1 = DROP k tvs /\ vs1 = DROP k vs /\
    EVERY (assignable_type (get_tenv cx)) tys1 /\
    EVERY (\g. case g of BaseTarget bt =>
      supported_target tops bindings bt /\ target_indices_pre_mods cenv.ce_modules cenv cx env bt
      | TupleTarget ts => F) todo /\
    body_const_cells_agree cenv.ce_modules cx env src /\
    expr_sim_inv_mods cenv.ce_modules cenv cx env src /\ src with gas_obs := [] = src /\
    call_evaluation_safe cx (int_calls_atargets todo) /\
    compile_tuple_store_all cenv tys1 todo ops1 cur = ((),sb) /\
    compile_tuple_store_all (gas_shadow_env T cenv) tys1 (MAP gas_shadow_assignment todo) ops1 shadow_cur =
      ((),shadow_sb) /\ gas_shadow_state cur shadow_cur /\
    fn_has_code cur sb func /\ fn_has_code shadow_cur shadow_sb shadow_func /\
    sa.cs_next_id <= cur.cs_next_id /\ sa.cs_next_var <= cur.cs_next_var /\
    local_ptrs_reserved cenv cur /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    ~block_is_terminated cur /\ ~u.vs_halted /\
    u.vs_current_bb = cur.cs_current_bb /\ u.vs_inst_idx = LENGTH cur.cs_current_insts /\
    return_buf_frame d cenv cur u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    storage_trace_domain cx st0 src.storage_trace /\
    lo <= p /\ p + type_memory_size_list tvs <= u.vs_alloca_next /\
    (type_memory_size_list tvs = 0 \/
     (?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < cur.cs_next_id /\
       b <= p /\ p + type_memory_size_list tvs <= b + sz /\
       (!n a len. local_region cenv src.scopes u n a len ==>
         b + sz <= a \/ a + len <= b)) \/
     (?n b sz. local_region cenv src.scopes u n b sz /\ b <= p /\
       p + type_memory_size_list tvs <= b + sz /\
       local_path_at cenv cx n (p-b) (TupleTV tvs))) /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem) /\
    (!i. i < LENGTH tys1 ==>
      ?x. EL i ops1 = Var x /\ not_fresh_at cur x /\ op_taint tu (Var x) = {} /\
          if is_word_type (EL i tys1) then
            lookup_var x u = SOME (typed_val_to_w256 (EL i tvs1) (EL i vs1)) /\
            op_prov Gu (Var x) = NONE
          else lookup_var x u =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (k+i) tvs)))) /\
               ptr_covers Gu tu x u (type_memory_size (EL i tvs1))) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gu x = FLOOKUP G0 x /\ op_taint tu (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv src u /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tu.t_mem ==> i IN tn0.t_mem)
End

(* Only the state relation and ghost invariant depend on the horizon. *)
Definition tuple_exact_cursor_at_def:
  tuple_exact_cursor_at (cenv,cx) (DF,lo,d,ctx,func) H src u Gu tu <=>
    stmt_state_rel H ctx func cenv cx src u /\
    storage_well_formed_on cx src (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx src Gu tu u
End

Definition tuple_exact_store_cursor_def:
  tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
    (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
    (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
    (cur,shadow_cur,src,u,Gu,tu) <=>
    tuple_exact_cursor_common (cenv,cx,env,tops,bindings)
      (lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
      (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
      (cur,shadow_cur,src,u,Gu,tu) /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
       tuple_exact_cursor_at (cenv,cx) (DF,lo,d,ctx,func) H src u Gu tu)
End

Theorem tuple_exact_cursor_head_operand:
  tuple_exact_cursor_common (cenv,cx,env,tops,bindings)
    (lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb) (es,s0,G0,tn0)
    (tys,tvs,vs) (todo,ty::tys1,tv::tvs1,v::vs1,op::ops1,k,p)
    (cur,shadow_cur,src,u,Gu,tu) ==>
  ?x. op = Var x /\ not_fresh_at cur x /\ op_taint tu (Var x) = {} /\
      (if is_word_type ty then
         lookup_var x u = SOME (typed_val_to_w256 tv v) /\
         op_prov Gu (Var x) = NONE
       else lookup_var x u = SOME (n2w (p + SUM (MAP type_memory_size (TAKE k tvs)))) /\
            ptr_covers Gu tu x u (type_memory_size tv))
Proof
  rewrite_tac[tuple_exact_cursor_common_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `!i. i < LENGTH _ ==> ?x. EL i _ = Var x /\ _`
    (qspec_then `0` mp_tac) >>
  simp[listTheory.EL, listTheory.LENGTH]
QED

(* The expanded boundary, with the independent obligations left as guards. *)
Theorem tuple_exact_store_cursor_iff:
  (tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
    (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
    (es,s0,G0,tn0) (tys,tvs,vs) (todo,tys1,tvs1,vs1,ops1,k,p)
    (cur,shadow_cur,src,u,Gu,tu) /\ callback /\ child_ok /\ admissible) <=>
    LIST_REL (\g ty. well_typed_atarget env g ty) todo tys1 /\
    LENGTH ops1 = LENGTH tys1 /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys1 tvs1 /\
    values_have_types tvs1 vs1 /\ tys1 = DROP k tys /\
    tvs1 = DROP k tvs /\ vs1 = DROP k vs /\
    EVERY (assignable_type (get_tenv cx)) tys1 /\
    EVERY (\g. case g of BaseTarget bt =>
      supported_target tops bindings bt /\ target_indices_pre cenv cx env bt
      | TupleTarget ts => F) todo /\
    callback /\ child_ok /\
    body_const_cells_agree [(NONE,tops)] cx env src /\
    expr_sim_inv cenv cx env src /\ src with gas_obs := [] = src /\
    admissible /\
    call_evaluation_safe cx (int_calls_atargets todo) /\
    compile_tuple_store_all cenv tys1 todo ops1 cur = ((),sb) /\
    compile_tuple_store_all (gas_shadow_env T cenv) tys1 (MAP gas_shadow_assignment todo) ops1 shadow_cur =
      ((),shadow_sb) /\ gas_shadow_state cur shadow_cur /\
    fn_has_code cur sb func /\ fn_has_code shadow_cur shadow_sb shadow_func /\
    sa.cs_next_id <= cur.cs_next_id /\ sa.cs_next_var <= cur.cs_next_var /\
    local_ptrs_reserved cenv cur /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    ~block_is_terminated cur /\ ~u.vs_halted /\
    u.vs_current_bb = cur.cs_current_bb /\ u.vs_inst_idx = LENGTH cur.cs_current_insts /\
    return_buf_frame d cenv cur u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    storage_trace_domain cx st0 src.storage_trace /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
      stmt_state_rel H ctx func cenv cx src u /\ storage_well_formed_on cx src (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx src Gu tu u) /\
    lo <= p /\ p + type_memory_size_list tvs <= u.vs_alloca_next /\
    (type_memory_size_list tvs = 0 \/
     (?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < cur.cs_next_id /\
       b <= p /\ p + type_memory_size_list tvs <= b + sz /\
       (!n a len. local_region cenv src.scopes u n a len ==>
         b + sz <= a \/ a + len <= b)) \/
     (?n b sz. local_region cenv src.scopes u n b sz /\ b <= p /\
       p + type_memory_size_list tvs <= b + sz /\
       local_path_at cenv cx n (p-b) (TupleTV tvs))) /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem) /\
    (!i. i < LENGTH tys1 ==>
      ?x. EL i ops1 = Var x /\ not_fresh_at cur x /\ op_taint tu (Var x) = {} /\
          if is_word_type (EL i tys1) then
            lookup_var x u = SOME (typed_val_to_w256 (EL i tvs1) (EL i vs1)) /\
            op_prov Gu (Var x) = NONE
          else lookup_var x u =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (k+i) tvs)))) /\
               ptr_covers Gu tu x u (type_memory_size (EL i tvs1))) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gu x = FLOOKUP G0 x /\ op_taint tu (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv src u /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tu.t_mem ==> i IN tn0.t_mem)
Proof
  pure_rewrite_tac[tuple_exact_store_cursor_def, tuple_exact_cursor_common_def,
                   tuple_exact_cursor_at_def] >>
  CONV_TAC (AC_CONV (CONJ_ASSOC,CONJ_COMM))
QED
