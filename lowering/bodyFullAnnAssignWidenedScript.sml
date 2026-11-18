(* Joint AnnAssign: physical layout of a widened aggregate RHS. *)
Theory bodyFullAnnAssignWidened
Ancestors
  assignRelayoutCaller annassignRelayoutSource annassignRelayoutFrag annassignRelayoutPost
  bodySimFull bodyPtrDefs exprSimSource exprSimHypsDefs gasOutcomeFullCompose
  loweringPosts exprLoweringProps exprOperandVar assignBasePtrBoundary
  externalReturnBounds exprSimAggregateChildren representationCleanPtr
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState
  compileEnv venomState venomMemDefs words arithmetic
  bodyFullAnnAssignMemoryPost bodyInvNoDalloca bodySim bodyExprPreFacts
  stmtSimDeclSource stmtSimDeclCompose stmtSimProps gasOutcomeFullStmts
  gasExemptCert vyperStorageTrace bodyMemoryDefs stmtLoweringMono freshWrites
  emitHelperProps fragExec allocaHistory typedMemoryCopy bodyDeclCopyMemory exprLowering stmtLowering
  immutableDeployAssignRanges annassignRelayoutContinue exprOpenTerminals

Theorem annassign_widened_full_layout:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 /\
  supported_expr tops e /\ ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops ==>
  ?stv.
    ~is_bytestring_type typ /\
    ~is_word_type (lowered_value_type ce e) /\
    ~is_bytestring_type (lowered_value_type ce e) /\
    post_value_type ce e = lowered_value_type ce e /\
    lowered_value_type ce e <> expr_type e /\ lowered_value_type ce e <> typ /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce typ = type_memory_size tyv /\
    type_memory_size stv <= type_memory_size tyv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
      value_has_type stv v /\ value_has_type tyv v /\
      val_wf stv v /\ val_wf tyv v /\
      val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >> drule_all assign_relayout_source_classify >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  qexists_tac `stv` >> simp[] >> rpt strip_tac >>
  metis_tac[annassign_relayout_read_layout]
QED

(* The strict physical layout supplies a real pointer variable and robust
   source encoding; the declaration's reserved allocation is disjoint. *)
Theorem annassign_widened_full_source:
  expr_post H ctx func ce cx e es sa sb s0 mid v op s /\
  post_value_type ce e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
  ptr_val_ok cx sty v op G tn s /\
  FLOOKUP s0.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id /\
  type_memory_size dtv <= sz /\ not_fresh_at sa p /\ lookup_var p s0 = SOME dw ==>
  ?xs sw.
    op = Var xs /\ lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    expr_val_at ce cx sty sa sb mid v (Var xs) s
Proof
  strip_tac >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)` by
    (irule expr_post_reserved_destination_source >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[]) >>
  `expr_val_at ce cx sty sa sb mid v op s /\
   stmt_state_rel H ctx func ce cx mid s` by fs[expr_post_def] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    (irule ptr_val_ok_read_covers >> simp[] >>
     goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (drule_all expr_val_at_frontier >> strip_tac >> gvs[]) >>
  qexistsl_tac [`xs`, `sw`] >> gvs[venomStateTheory.eval_operand_def] >>
  fs[ptr_val_ok_def, ptr_mem_ok_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

(* Enrich only the successful RHS post.  The supplied post, including its
   allocation/taint frame, and the complete exceptional post are retained. *)
Theorem annassign_widened_full_rhs_source:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,t0,G0,tn0) Q R /\
  post_value_type ce e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  0 < type_memory_size stv /\
  (!gs v mid. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
    value_has_type dtv v /\ val_wf dtv v /\
    val_footprint stv v = type_memory_size stv) /\
  FLOOKUP t0.vs_allocas aid = SOME (w2n dw,sz) /\ aid < a.cs_next_id /\
  type_memory_size dtv <= sz /\ not_fresh_at a p /\ lookup_var p t0 = SOME dw /\
  (!H v mid G tn t. Q H (INL v) mid G tn t ==>
    expr_post H ctx func ce cx e es a b t0 mid v op t /\
    ptr_val_ok cx sty v op G tn t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,t0,G0,tn0)
    (\H res mid G tn t. Q H res mid G tn t /\
      !v. res = INL v ==> value_has_type dtv v /\ val_wf dtv v /\
        ?xs sw.
          op = Var xs /\ lookup_var xs t = SOME sw /\ lookup_var p t = SOME dw /\
          FLOOKUP t.vs_allocas aid = SOME (w2n dw,sz) /\
          ptr_covers G tn xs t (type_memory_size stv) /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory stv v (w2n sw) mem) /\
          w2n sw + type_memory_size stv < dimword (:256) /\
          w2n dw + type_memory_size dtv < dimword (:256) /\
          w2n sw + type_memory_size stv <= t.vs_alloca_next /\
          (w2n sw + type_memory_size stv <= w2n dw \/
           w2n dw + type_memory_size dtv <= w2n sw) /\
          expr_val_at ce cx sty a b mid v (Var xs) t) R
Proof
  strip_tac >> irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `value_has_type dtv v /\ val_wf dtv v /\
   val_footprint stv v = type_memory_size stv` by
    (qpat_x_assum `!gs v mid. _` irule >>
     qexists_tac `xs` >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  simp[] >>
  qpat_x_assum `!H v mid G tn t. _` drule_all >> strip_tac >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [ADD_COMM] annassign_widened_full_source) >>
  simp[] >> disch_then drule_all >> simp[]
QED

(* The two implementation callbacks are literal contracts.  The common
   allocation/RHS prefix is a theorem dependency, never an assumption. *)
Theorem annassign_widened_full_execution:
  (!(H0 : (bool # 256 word # type_value) list # num list) ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v
   n sz aid0 start lo explicit PG G tn.
    compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
      dty sty (type_memory_bytes ce dty) sa = ((),sf) /\
    ~is_word_type dty /\ ~is_word_type sty /\
    stmt_state_rel H0 ctx func ce cx mid s /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ alloca_history func s /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        len = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size dtv <= sz /\ n < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa p /\
    lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid0 = SOME (w2n dw,sz) /\ aid0 < sa.cs_next_id /\
    ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw+n < dimword (:256) /\
    w2n dw+type_memory_size dtv < dimword (:256) /\
    (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
    (src_loc = SOME LocMemory ==>
      expr_val_at ce cx sty start sa mid v (Var xs) s) /\
    (src_loc <> SOME LocMemory ==>
      w2n sw+n <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n sw) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u sm Gu tnu t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      (!(H : (bool # 256 word # type_value) list # num list).
        stmt_state_rel H ctx func ce cx mid s ==>
        stmt_state_rel H ctx func ce cx mid u) /\
      (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
        ghost_inv_at D lo d ce cx mid Gu tnu u) /\
      alloca_frame ce mid sa s ce mid u /\
      (!aid off len i.
        FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region ce mid.scopes s name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tnu.t_mem ==> i IN tn.t_mem) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      s.vs_alloca_next <= u.vs_alloca_next /\
      sa.cs_next_id <= sm.cs_next_id /\ local_ptrs_reserved ce sm /\
      (!x. not_fresh_at sa x ==>
        not_fresh_at sm x /\ lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)) /\
      lookup_var p u = SOME dw /\ ptr_covers Gu tnu p u sz /\
      typed_copy_state_frame sm (w2n dw) (type_memory_size dtv) u t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
        val_in_memory dtv v (w2n dw) mem) /\
      tf.t_stor = tnu.t_stor /\ tf.t_trans = tnu.t_trans /\ tf.t_imm = tnu.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
        (i IN tf.t_mem <=> i IN tnu.t_mem)) /\
      (!x. not_fresh_at sm x ==>
        lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
        op_taint tf (Var x) = op_taint tnu (Var x)) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)) /\
  (!(H : (bool # 256 word # type_value) list # num list) D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf
   id p sz w inst n tyv v sc rest lctx.
    new_variable id tyv v mid = (INL (),out) /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    FLOOKUP old.ce_vars id = NONE /\
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
    local_ptrs_reserved ce b /\ not_fresh_at b p /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
    n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
    val_wf tyv v /\ value_has_type tyv v /\
    typed_copy_state_frame b (w2n w) n s t /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame old es sa s0 ce mid s /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP s.vs_allocas aid = SOME ent) /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
    cenv_top_ext old ce out.scopes /\
    stmt_state_rel H ctx func ce cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce cx out Gf tf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce out t /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)) /\
  body_inv tops ctx old cx /\ supported_expr tops e /\
  type_widens_to env.type_defs (expr_type e) typ /\
  ~is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes old typ < 2 ** 64 /\
  FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  (!sa ce r. declare_local old id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    ~(lowered_value_type ce e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e))) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ old
    (stmt_env old lctx ret_ty (AnnAssign id typ e))
    (stmt_env old lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  strip_tac >>
  qpat_x_assum `!H0 ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v n sz aid0 start lo explicit PG G tn. compile_assign_value _ _ _ _ _ _ _ _ _ _ = _ /\ _ ==> _`
    (mk_asm "dispatch") >>
  qpat_x_assum `!H D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf id p sz w inst n tyv v sc rest lctx. _`
    (mk_asm "install") >>
  rewrite_tac[stmt_frag_full_def] >>
  map_every qx_gen_tac [`st0`,`sa`,`sf`,`shadow_sa`,`shadow_sf`,`s0`,`G0`,`tn0`,`ce`] >>
  strip_tac >>
  `old.ce_alloca_locals /\ ~ctx_has_dalloca ctx` by
    (conj_tac >- fs[body_inv_def] >> drule body_inv_no_dalloca >> simp[]) >>
  drule_all annassign_full_prefix_parts >> strip_tac >>
  qpat_x_assum `!sa ce r. declare_local _ _ _ _ = _ ==> _` drule >>
  strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  `type_memory_bytes ce typ = type_memory_bytes old typ` by simp[] >>
  `ce.ce_func_return_type = build_func_return_type tops /\
   supported_program tops /\ get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `type_memory_bytes ce typ < 2 ** 64` by fs[] >>
  drule_all annassign_widened_full_layout >> strip_tac >>
  `~(has_length_word typ /\ is_empty_value_expr e)` by
    (qpat_x_assum `~is_bytestring_type (lowered_value_type ce e)` mp_tac >>
     qpat_x_assum `lowered_value_type ce e <> expr_type e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `e` >>
     simp[is_empty_value_expr_def,lowered_value_type_def]
     >~ [`Builtin ety builtin args`]
     >- (Cases_on `builtin` >> simp[is_empty_value_expr_def,lowered_value_type_def])
     >~ [`TypeBuiltin ety builtin ts args`]
     >- (Cases_on `builtin` >> simp[is_empty_value_expr_def,lowered_value_type_def])
     >> rename1 `Literal ety lit` >> Cases_on `lit` >>
     simp[is_empty_value_expr_def,lowered_value_type_def] >> Cases_on `ety` >>
     simp[lowered_value_type_def] >> qmatch_goalsub_rename_tac `Literal (BaseT bty) _` >> Cases_on `bty` >>
     simp[lowered_value_type_def] >> qmatch_goalsub_rename_tac `Literal (BaseT (BytesT bnd)) _` >> Cases_on `bnd` >>
     simp[lowered_value_type_def,is_bytestring_type_def]) >>
  gnvs[] >> suspend "prefix"
QED

Resume annassign_widened_full_execution[prefix]:
  markerLib.RESUME_TAC >> irule gas_outcome_full_initial_domain >> simp[] >> conj_tac
  >- irule (cj 1 vyperStorageTraceTheory.evaluate_storage_trace_frame) >>
  strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _ /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes old typ < dimword (:256)` by simp[dimword_def] >>
  qpat_assum `declare_local old id typ sa = (ce,r)`
    (mp_then Any mp_tac (SRULE [] annassign_full_alloc_rhs_prefix)) >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac) >>
  suspend "rhs"
QED

Resume annassign_widened_full_execution[rhs]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    annassign_widened_full_rhs_source >>
  simp[] >>
  disch_then (qspecl_then [`type_memory_bytes old typ`,`stv`,`p`,`op`,`w`,`tyv`,
    `ce`,`b`,`sa.cs_next_id`,`a`] mp_tac) >>
  (impl_tac >- (asm_x "dispatch" kall_tac >> asm_x "install" kall_tac >>
    simp[] >> rpt strip_tac >> gvs[] >>
    first_x_assum drule >> simp[])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rhs_post _` >>
  suspend "source"
QED

Resume annassign_widened_full_execution[source]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_zero_prefix >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- simp[] >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
    (mp_then Any (qspecl_then [`id`,`e`] SUBST1_TAC) eval_annassign_action) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res mid G tn t. rhs_post H res mid G tn t /\
    ~t.vs_halted /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ rhs_post _` (irule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      simp[bodyPtrDefsTheory.stmt_exit_ptr_def,exprSimDefsTheory.halt_exit_def] >>
      fs[exprSimDefsTheory.halt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  BETA_TAC >> rpt strip_tac >> suspend "continuation"
QED

Resume annassign_widened_full_execution[continuation]:
  markerLib.RESUME_TAC >>
  qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
    (assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `rhs_post` >>
  Cases_on `res` >>
  qpat_x_assum `(\H res mid G tn t. _) _ _ _ _ _ _` mp_tac >>
  BETA_TAC >> simp_tac (srw_ss()) [] >> strip_tac >>
  suspend "new_variable"
QED

Resume annassign_widened_full_execution[new_variable]:
  markerLib.RESUME_TAC >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  qabbrev_tac `out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := x; popped := []|>))::rest` >>
  `out.gas_obs = []` by simp[Abbr `out`] >>
  `new_variable id tyv x mid = (INL (),out)` by
    (qpat_assum `!tail. new_variable _ _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >>
     simp_tac (srw_ss()) [Abbr `out`]) >>
  suspend "suffix"
QED

Resume annassign_widened_full_execution[suffix]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gu,tu)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\ stmt_state_rel H ctx func ce cx out u /\
      storage_well_formed_on cx out (FST H) /\ return_buf_frame d ce sf u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx out Gu tu u /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z u = SOME w) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      (!z. not_fresh_at sa z ==> FLOOKUP Gu z = FLOOKUP G0 z /\
        op_taint tu (Var z) = op_taint tn0 (Var z)) /\
      alloca_frame old es sa s0 ce out u /\
      (!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tu.t_mem ==> i IN tn0.t_mem)` by
    (match_mp_tac (GEN_ALL annassign_memory_full_suffix_post) >>
     qexistsl_tac [`xs`,`x`,`type_memory_bytes old typ`,`sw`,
       `lowered_value_type old e`,`stv`,`a`,`vv_location vv`,`sc`,`rest`,
       `p`,`type_memory_size stv`,`mid`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes old typ))] [p]`,
       `id`,`w`,`typ`,`tyv`,`b`,`storage_trace_horizon mid.storage_trace`] >>
     conj_tac >- asm "dispatch" MATCH_ACCEPT_TAC >>
     conj_tac >- asm "install" MATCH_ACCEPT_TAC >>
     asm_x "dispatch" kall_tac >> asm_x "install" kall_tac >>
     `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     drule_all immutable_assign_copy_metadata >> strip_tac >>
     `not_fresh_at b xs` by
       (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
          (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
     `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid t /\
      storage_well_formed_on cx mid (FST (storage_trace_horizon mid.storage_trace))` by
       fs[expr_post_def] >>
     `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
     `mid with gas_obs := [] = mid` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     `value_has_type stv x /\ val_wf stv x` by
       (qpat_assum `!gs v mid. _`
          (qspecl_then [`gas_explicit marks entry.vs_gas_readings`,`x`,`mid`] mp_tac) >>
        qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
        simp_tac (srw_ss()) [] >> simp[]) >>
     `a.cs_next_id <= b.cs_next_id` by
       (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
         (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     `b.cs_next_var <= sf.cs_next_var` by
       (qpat_assum `compile_assign_value ce _ _ _ _ _ _ _ _ b = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        metis_tac[cj 1 ci_mono_stmt_helpers,ci_mono_def,pairTheory.SND]) >>
     `sa.cs_next_id < b.cs_next_id /\ sa.cs_next_id <= b.cs_next_id` by decide_tac >>
     simp[Abbr `out`,ADD_COMM,venomInstTheory.mk_inst_def] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           drule >> simp[expr_post_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!aid off len i. _` irule >>
         simp[ADD_COMM] >> qexists_tac `aid` >> simp[ADD_COMM] >>
         rpt strip_tac >> first_x_assum drule >> decide_tac) >>
     `~(lowered_value_type ce e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type ce e) /\
        arg_type_fits (lowered_value_type ce e) (expr_type e))` by simp[] >>
     qpat_assum `compile_expr ce (expr_type e) e a = (vv,sv)`
       (mp_then (Pat `compile_expr _ _ _ _ = _`)
         (qspecl_then [`cx`,`env`,`es`] mp_tac) residual_call_compile_location) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `~block_is_terminated b` by (drule_all unwrap_value_open >> simp[]) >>
     irule compile_assign_memory_relayout_open >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[]) >>
  suspend "pure"
QED

Resume annassign_widened_full_execution[pure]:
  markerLib.RESUME_TAC >> (
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gu`,`out`,`INL ()`,`u`,`tu`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  gen_tac >> disch_tac >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  `out with gas_obs := [] = out` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `!H. valid_horizon cx st0 H out.storage_trace ==> _` drule >>
  simp[ADD_COMM] >> strip_tac >>
  pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  metis_tac[ADD_COMM])
QED

Finalise annassign_widened_full_execution
