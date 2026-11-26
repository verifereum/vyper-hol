(* The checked cast returns the existing buffer without writing it. *)
Theory bodyConvertBytesCastPostMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  bodyFullConvertEndpointPosts assignTuplePtrLoadStep exprSimConvertBytes
  exprSimStack exprSimMemDefs exprSimProps exprSimWordArgs stateFrame valueCopyBytes
  supportedExprTraverse loweringShapeDefs loweringStateRelDefs
  loweringPosts bodyPtrDefs ptrDiscipline typeLayoutProps
  exprLowering vyperAST vyperContext vyperState venomState context
  vyperInterpreter vyperStorageFootprint words

Theorem cast_vv_post_mods[local]:
  expr_post H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid v op q /\
  storage_well_formed_on cx mid (FST H) /\
  immutable_frame_mods func ce cx mid q /\ ~is_word_type dst ==>
  vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid (Value v) (LocatedValue dst (mk_ptr op LocMemory)) q
Proof
  strip_tac >>
  `vv_post H ctx func ce cx (TypeBuiltin dst Convert dst [e]) es sa sb s0 mid
     (Value v) (LocatedValue dst (mk_ptr op LocMemory)) q` by
    (irule (SIMP_RULE (srw_ss()) [post_value_type_def, expr_type_def]
       (Q.INST [`e` |-> `TypeBuiltin dst Convert dst [e]`] vv_post_stack_as_memory)) >>
     simp[] >> qexists_tac `dst` >> irule dynamic_word_vv_post >> simp[]) >>
  fs[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
  first_assum ACCEPT_TAC
QED

Theorem bytes_convert_cast_post_mods:
  expr_post_mods H ctx func ce cx e es sa sm s0 mid v (Var src) t /\
  storage_well_formed_on cx mid (FST H) /\
  ghost_inv_at_mods D lo d ce cx mid G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  ptr_val_ok cx (post_value_type ce e) v (Var src) G tn t /\
  ptr_buf_ok ce e (Var src) G t /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  post_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME pt /\ value_has_type pt v /\
  convert_result cx (expr_type e) dst v = INL vout /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  type_memory_bytes ce dst = type_memory_size tout /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size tout <= type_memory_size rt /\
  eval_operand (Var src) t = SOME w /\
  (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
  not_fresh_at sm src /\ local_ptrs_reserved ce sm /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  state_frame q = state_frame (t with vs_inst_idx := q.vs_inst_idx) /\
  q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x t /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  alloca_history func q /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid (Value vout) (LocatedValue dst (mk_ptr (Var src) LocMemory)) q /\
  vv_store_bound cx dst dst mid (Value vout)
    (LocatedValue dst (mk_ptr (Var src) LocMemory)) q /\
  q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
  s0.vs_alloca_next <= q.vs_alloca_next /\
  ghost_inv_at_mods D lo d ce cx mid Gf tnf q /\
  ptr_vv_ok cx dst (Value vout) (LocatedValue dst (mk_ptr (Var src) LocMemory)) mid Gf tnf q /\
  ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) (Var src) Gf q /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `~is_word_type (expr_type e) /\ ~is_word_type dst` by
    metis_tac[is_bytestring_word_type] >>
  `q = (t with vs_inst_idx := q.vs_inst_idx) with vs_vars := q.vs_vars` by
    (qpat_assum `state_frame q = _` (mp_tac o SYM) >>
     pure_rewrite_tac[state_frame_eq_reconstruct] >>
     simp[Once EQ_SYM_EQ]) >>
  `q.vs_memory = t.vs_memory /\ q.vs_data_section = t.vs_data_section /\
   q.vs_allocas = t.vs_allocas /\ q.vs_alloca_next = t.vs_alloca_next /\
   q.vs_call_ctx = t.vs_call_ctx /\ q.vs_accounts = t.vs_accounts /\
   q.vs_transient = t.vs_transient /\ q.vs_immutables = t.vs_immutables /\
   q.vs_initial_fmp = t.vs_initial_fmp /\ q.vs_fmp = t.vs_fmp` by
    (pop_assum SUBST1_TAC >> simp[]) >>
  qpat_x_assum `q = _ with vs_vars := _` kall_tac >>
  `eval_operand (Var src) q = SOME w /\ FLOOKUP Gf src = FLOOKUP G src /\
   op_taint tnf (Var src) = op_taint tn (Var src)` by
    metis_tac[eval_operand_def] >>
  `val_wf tout vout` by (irule convert_bytestring_wf >> metis_tac[]) >>
  `val_store_size tout vout <= type_memory_size tout` by simp[val_store_size_le] >>
  `ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) (Var src) Gf q` by
    (simp[ptr_buf_ok_def,lowered_value_type_def,expr_type_def] >> strip_tac >>
     `type_memory_size rt <> 0` by decide_tac >>
     qpat_assum `ptr_buf_ok ce e (Var src) G t` (mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
     disch_then (qspec_then `w` mp_tac) >> simp[] >>
     disch_then (qx_choosel_then [`b`,`sz`] strip_assume_tac) >>
     qexistsl_tac [`b`,`sz`] >> simp[] >> decide_tac) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     pure_rewrite_tac[allocas_below_fmp_def] >>
     asm_rewrite_tac[]) >>
  simp[] >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "bound" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "pointer" >>
  irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G`,`tn`] >> simp[] >> metis_tac[not_fresh_at_mono]
QED

Resume bytes_convert_cast_post_mods[post]:
  drule expr_post_state >> strip_tac >>
  `stmt_state_rel H ctx func ce cx mid q` by
    (irule stmt_state_rel_old_vars_frame_ptr >> qexistsl_tac [`t`,`sm`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `expr_post H ctx func ce cx e es sa sb s0 mid v (Var src) q` by
    (irule convert_readonly_expr_post >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w`,`t`,`sm`,`Var src`] >> simp[] >> metis_tac[]) >>
  `expr_post H ctx func ce cx (TypeBuiltin dst Convert dst [e])
     es sa sb s0 mid vout (Var src) q` by
    (irule convert_bytestring_expr_post >> simp[expr_type_def] >>
     qexistsl_tac [`e`,`pt`,`v`] >> simp[]) >>
  irule cast_vv_post_mods >> simp[] >>
  irule immutable_frame_mods_exterior_frame >>
  qexistsl_tac [`mid`,`t`,`sm`] >> simp[] >> metis_tac[]
QED

Resume bytes_convert_cast_post_mods[bound]:
  simp[vv_store_bound_def,mk_ptr_def,read_result_def,return_def] >> decide_tac
QED

Resume bytes_convert_cast_post_mods[ghost]:
  irule ghost_inv_at_mods_exterior_frame >>
  qhdtm_assum `ghost_inv_at_mods` (irule_at Any) >>
  qexists_tac `sm` >> simp[]
QED

Resume bytes_convert_cast_post_mods[pointer]:
  drule_all convert_bytestring_memory >> strip_tac >>
  qhdtm_x_assum `ptr_val_ok` mp_tac >>
  simp[ptr_val_ok_def,ptr_mem_ok_def] >> strip_tac >>
  simp[ptr_vv_ok_def,ptr_mem_ok_def,mk_ptr_def,read_result_def,return_def] >>
  strip_tac >>
  `type_memory_size tout <> 0` by
    (strip_tac >> `val_store_size tout vout = 0` by decide_tac >>
     mp_tac (Q.SPECL [`tout`,`vout`] val_footprint_le_store_size) >> simp[]) >>
  qpat_x_assum `ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) _ _ _` mp_tac >>
  simp[ptr_buf_ok_def,lowered_value_type_def,expr_type_def] >>
  disch_then (qx_choosel_then [`b`,`sz`] strip_assume_tac) >>
  qexistsl_tac [`b`,`sz`] >> simp[] >> decide_tac
QED

Finalise bytes_convert_cast_post_mods
