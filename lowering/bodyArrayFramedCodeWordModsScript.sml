(* Force the selected runtime-code element without changing its linked frame. *)
Theory bodyArrayFramedCodeWordMods
Ancestors
  bodyIfExpWordReadMods bodyLocalCopyPhysicalRhsMods exprPtrCodeCopyLoad
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPostsMods
  exprSimUnwrapProps exprSimProps exprSimCopy exprLowering bodyPtrDefs
  compileEnv loweringPosts loweringStateRelDefs stateRelProj
  exprOperandVar ptrDiscipline exprSimMemDefs immutableCopyExecution
  fragGasOriginPtr fragGasOriginPtrDead vyperStorageFootprint
  vyperAST venomState finite_map pred_set words context valueEncodingDefs
  bodyFullShadowBodyInv bodyPtrSignedConvertSourceFrame freshWrites

val empty_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {}|>``;

val readonly = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP (Gf:string |-> num # num) x = FLOOKUP (G:string |-> num # num) x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

Theorem framed_code_word_run[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw (LocatedValue tag p) s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue tag p) ee G tn s /\
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\
  is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  value_has_type rt v /\ read_result cx raw ee = (INL v,ee) /\
  unwrap_value ce (LocatedValue tag p) sm = (op,sb) /\
  copy_old_operand sm p.ptr_operand /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ ^readonly
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor` >> gvs[] >>
  qpat_assum `~ce.ce_is_ctor`
    (fn th => drule_all_then strip_assume_tac
      (SIMP_RULE (srw_ss()) [th] local_copy_raw_code_source_mods)) >> gvs[] >>
  `compile_ptr_load F ce.ce_imm_alloca LocCode p.ptr_operand sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def] >> strip_tac) >>
  `compile_imm_load_word F ce.ce_imm_alloca p.ptr_operand sm = (op,sb)` by
    fs[compile_ptr_load_def] >>
  `immutable_copy_read F w s = typed_val_to_w256 rt v` by
    (drule_all val_in_memory_word_type >> simp[immutable_copy_read_def,mem_word_at_def]) >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (qspecl_then [`func`,`PG`,`G`,`^empty_dead`] strip_assume_tac)
    code_copy_runtime_load >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >> simp[] >> strip_tac >>
  qhdtm_x_assum `copy_runtime_frame` (strip_assume_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
  `alloca_inv s` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `w2n w <= LENGTH s.vs_data_section` by decide_tac >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    (word_arm_loaded_path |> Q.INST [`loc` |-> `LocCode`,`ctor` |-> `F`] |>
     SIMP_RULE (srw_ss()) []) >>
  qexistsl [`u`,`Gf`,`tnf`] >> simp[] >> gen_tac >>
  irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC
QED

Theorem framed_code_word_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\ ^readonly ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op u /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf u
Proof
  strip_tac >>
  qhdtm_x_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sm`] >> simp[]) >>
  reverse conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sm`,`tn`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]) >>
  simp[expr_post_mods_def, expr_post_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

Theorem framed_code_word_read_mods:
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME rt /\
  value_has_type rt v /\ read_result cx raw ee = (INL v,ee) /\
  unwrap_value ce (LocatedValue ann p) sm = (op,sb) /\
  copy_old_operand sm p.ptr_operand /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Subscript ann obj idx) es sa sm s0 ee raw
      (LocatedValue ann p) s /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx ann raw (LocatedValue ann p) ee G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee v op u /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u) /\
    expr_store_bound cx ann v op u /\ ptr_val_ok cx ann v op Gf tf u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac)
    (framed_code_word_run |> Q.INST [`e` |-> `Subscript ann obj idx`] |>
     REWRITE_RULE [post_value_type_def,expr_type_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee v op u /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     match_mp_tac (framed_code_word_post |> Q.INST [`e` |-> `Subscript ann obj idx`,
         `vv` |-> `LocatedValue ann p`] |>
       REWRITE_RULE [post_value_type_def,expr_type_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
     rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[expr_store_bound_word,ptr_val_ok_word] >>
  fs[allocas_below_fmp_def] >> metis_tac[]
QED
