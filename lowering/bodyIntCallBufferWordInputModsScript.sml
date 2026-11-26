Theory bodyIntCallBufferWordInputMods
Ancestors
  bodyIfExpWordReadMods bodyForRangeScalarFrameMods bodyFullUnwrapRun exprSimUnwrap
  bodyPtrSignedConvertSourceFrame bodyFullPostsMods bodyFullShadowBodyInv
  loweringPosts loweringStateRelDefs exprSimUnwrapProps exprOperandVar
  exprSimCopy compileEnv exprLoweringProps exprLowering exprSimDefs
  exprSimProps exprSimMemDefs context stateRelProj freshWrites
  appendStorageGhostPtr reasonCopySourcePtr bodyPtrDefs ptrDiscipline
  fragGasOriginPtr fragGasOriginPtrDead reasonSourceProps vyperStorageFootprint
  vyperAST vyperState venomState valueEncodingDefs finite_map pred_set words arithmetic

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>``;

val read_frame = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at ca x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP (Gf : string |-> num # num) x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

val ctor_read = ``
  ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt v (w2n w) mem)``;

val word_endpoint = ``
  read_result cx tv ee = (INL v,ee) /\
  gas_origin_ptr_path (^no_dead,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  alloca_history func u /\ ^read_frame``;

Theorem buffer_word_read_at[local]:
  unwrap_value ce vv ca = (op,cu) /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_post_mods H ctx func ce cx e es sa ca s0 ee tv vv s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\ (^ctor_read) /\
  copy_old_operand ca (vv_operand vv) /\ local_ptrs_reserved ce ca /\
  fn_has_code ca cu func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v u Gf tf. ^word_endpoint
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce e = expr_type e` by simp[] >>
  Cases_on `vv`
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def,comp_return_def] >>
      disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >>
      rename1 `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ (StackValue tag x) _` >>
      `?v. read_result cx tv ee = (INL v,ee) /\
           eval_operand x s = SOME (typed_val_to_w256 rt v)` by
        (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
         qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
         simp[vv_holds_mods_def,vv_holds_def,expr_val_rel_def] >>
         strip_tac >> qexists `v` >> simp[]) >>
      `op_taint tn x = {} /\ op_prov G x = NONE` by
        (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
         simp[ptr_vv_ok_def,ptr_val_ok_def]) >>
      qexistsl [`v`,`s`,`G`,`tn`] >> simp[cj 1 gas_origin_ptr_path_rules]) >>
  rename1 `LocatedValue tag p` >>
  drule word_arm_location >> simp[] >> strip_tac >>
  qpat_x_assum `tag = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[unwrap_value_def] >> disch_tac >>
  qpat_x_assum `copy_old_operand _ _` (assume_tac o REWRITE_RULE [vv_operand_def]) >>
  drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
    (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet) >>
  disch_then (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  (impl_tac >-
    (qpat_assum `post_value_type _ _ = _` (fn th =>
       qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [th]) >>
       qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` (assume_tac o REWRITE_RULE [th])) >>
     simp[] >>
     qpat_x_assum `ce.ce_is_ctor /\ vv_location _ = _ ==> _` mp_tac >>
     simp[vv_location_def,vv_operand_def] >> metis_tac[ADD_COMM])) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at ca x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at ca x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at ca x ==> _ /\ _ /\ _` drule >> simp[]
QED

Theorem buffer_word_post_at[local]:
  vv_post_mods H ctx func ce cx e es sa ca s0 ee tv vv s /\
  local_ptrs_reserved ce ca /\ sa.cs_next_var <= ca.cs_next_var /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at ca x ==> lookup_var x u = lookup_var x s) ==>
  expr_post_mods H ctx func ce cx e es sa cu s0 ee v op u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`ca`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`ca`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[not_fresh_at_mono]) >>
  simp[expr_post_mods_def,expr_post_def,expr_val_rel_def,expr_val_at_def,expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

Theorem buffer_word_endpoint_horizon[local]:
  vv_post_mods H ctx func ce cx e es sa ca s0 ee tv vv s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  local_ptrs_reserved ce ca /\ sa.cs_next_var <= ca.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\ (^read_frame) ==>
  expr_post_mods H ctx func ce cx e es sa cu s0 ee v op u /\
  ghost_inv_at_mods Dh lo d ce cx ee Gf tf u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule buffer_word_post_at >> simp[] >> qexistsl [`ca`,`s`,`tv`,`vv`] >>
      simp[] >> rpt strip_tac >> qpat_assum `!x. not_fresh_at ca x ==> _` drule >> simp[]) >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`ca`,`tn`] >>
  simp[] >> rpt conj_tac >>
  qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])
QED

(* The actual expression finishes at ci. The vv resources here have already
   crossed the destination allocation: only the load from ca to cu runs. *)
Theorem intcall_buffer_word_input_mods:
  compile_expr ce ty e sa = (vv,ci) /\ ci.cs_next_var <= ca.cs_next_var /\
  unwrap_value ce vv ca = (op,cu) /\
  is_word_type dty /\ type_widens_to tenv (expr_type e) dty /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa ca s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\ (^ctor_read) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_has_code ca cu func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  not_fresh_at ca dst /\ lookup_var dst s = SOME dw /\
  ptr_covers G tn dst s cap /\ 32 <= cap /\
  w2n dw + cap < dimword (:256) /\ w2n dw + cap <= s.vs_alloca_next ==>
  ?v dtv u Gf tf.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    eval_operand op u = SOME (typed_val_to_w256 dtv v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    lookup_var dst u = SOME dw /\ ptr_covers Gf tf dst u cap /\
    ptr_covers Gf tf dst u 32 /\ w2n dw + 32 < dimword (:256) /\
    w2n dw + 32 <= u.vs_alloca_next /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ alloca_history func u /\ alloca_inv u /\
    ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
    u.vs_inst_idx = LENGTH cu.cs_current_insts /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ (^read_frame) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa cu s0 ee v op u /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u) /\
    expr_store_bound cx (post_value_type ce e) v op u /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac type_widens_to_word >>
  qpat_x_assum `expr_type e = dty` (SUBST_ALL_TAC o SYM) >>
  drule_then strip_assume_tac compile_expr_extends >>
  `sa.cs_next_var <= ca.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce ca` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x)` by
    metis_tac[not_fresh_at_mono] >>
  `copy_old_operand ci (vv_operand vv)` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[copy_old_operand_def]) >>
  `copy_old_operand ca (vv_operand vv)` by metis_tac[copy_old_operand_mono] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) buffer_word_read_at >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func ce cx e es sa cu s0 ee v op u /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `u.vs_inst_idx = _` kall_tac >>
     irule buffer_word_endpoint_horizon >> simp[] >>
     qexistsl [`G`,`ca`,`s`,`tn`,`tv`,`vv`] >> simp[]) >>
  `alloca_inv u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def,expr_post_def] >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `ptr_covers Gf tf dst u cap` by
    (irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`ca`,`tn`] >>
     simp[] >> rpt strip_tac >> qpat_assum `!x. not_fresh_at ca x ==> _` drule >> simp[]) >>
  `ptr_covers Gf tf dst u 32` by metis_tac[ptr_covers_mono] >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_halted = s.vs_halted /\
   u.vs_fmp = s.vs_fmp /\ u.vs_initial_fmp = s.vs_initial_fmp` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  `w2n dw + 32 < dimword (:256) /\ w2n dw + 32 <= u.vs_alloca_next` by decide_tac >>
  qpat_assum `u.vs_inst_idx = _` (fn th =>
    qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (assume_tac o REWRITE_RULE [th])) >>
  qexistsl [`v`,`rt`,`u`,`Gf`,`tf`] >>
  simp[expr_store_bound_word,ptr_val_ok_word] >>
  rpt conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[])
  >- (simp[allocas_below_fmp_def] >> fs[allocas_below_fmp_def]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> `not_fresh_at ca x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. not_fresh_at ca x ==> _` drule >> simp[]
QED
