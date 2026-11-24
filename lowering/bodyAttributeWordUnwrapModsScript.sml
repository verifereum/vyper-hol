(* Force a reached linked Attribute word by executing its actual load. *)
Theory bodyAttributeWordUnwrapMods
Ancestors
  bodyIfExpWordReadMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  bodySimStmtFacts bodyPtrSignedConvertSourceFrame exprBodyPreProps bodyWriteSubscriptSourceMods
  exprSimAttribute exprSimUnwrap exprOperandVar exprSimCopy reasonSourceProps
  bodyFullPostsMods bodyFullShadowBodyInv loweringPosts loweringStateRelDefs
  exprSimHypsDefs bodyPtrDefs exprSimDefs exprSimMemDefs exprSimProps ptrDiscipline
  fragGasOriginPtr fragGasOriginPtrDead bodyLocalCopyPhysicalRhsMods
  exprLowering exprLoweringProps compileEnv context stateRelProj freshWrites
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeEvalCaseProofs
  vyperTypeSystem vyperStorageFootprint
  vyperInterpreter vyperState vyperAST vyperStorageTrace venomState
  valueEncodingDefs finite_map pred_set pair
Libs monadsyntax

Theorem attribute_word_read_type[local]:
  expr_body_pre_mods mods ce cx env (Attribute ann obj fld) es /\
  eval_expr cx (Attribute ann obj fld) (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) ann = SOME rt /\ value_has_type rt v
Proof
  strip_tac >>
  `bind (eval_expr cx (Attribute ann obj fld)) (read_result cx)
      (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  `expr_body_pre_mods mods ce cx env (Attribute ann obj fld) (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP (SPEC_ALL env_consistent_type_defs_get_tenv)) >>
  fs[value_runtime_typed_def, expr_type_def]
QED

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>``;

val read_only = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (Gf : string |-> num # num) x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

Theorem attribute_word_load[local]:
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sm /\
  copy_old_operand sm p.ptr_operand /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sm s0 ee tv (LocatedValue ann p) s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx ann ann ee tv (LocatedValue ann p) s /\
  ptr_vv_ok cx ann tv (LocatedValue ann p) ee G tn s /\
  (ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) ann = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v u Gf tf.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ ^read_only
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce (Attribute ann obj fld) = ann` by simp[expr_type_def] >>
  `p.ptr_location <> LocCalldata` by (drule_all word_arm_location >> simp[]) >>
  qpat_assum `ghost_inv_at_mods Dh _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`sb`,`rt`,`op`,`PG`] mp_tac) >>
  (impl_tac >- (fs[lowered_value_type_def,expr_type_def,arithmeticTheory.ADD_COMM] >>
                disch_tac >>
                qpat_x_assum `_ /\ _ ==> ?v. read_result _ _ _ = _ /\ _` mp_tac >> simp[] >>
                disch_then (qx_choose_then `v_read` strip_assume_tac) >>
                qexists_tac `v_read` >> simp[] >>
                first_x_assum (qspec_then `rt` mp_tac) >> simp[])) >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

Theorem attribute_word_read_post[local]:
  vv_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sm s0 ee tv vv s /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  expr_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee v op u
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sm`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  simp[expr_post_mods_def,expr_post_def,expr_type_def,
       expr_val_rel_def,expr_val_at_def,expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

Theorem attribute_word_unwrap_endpoint_mods:
  expr_body_pre_mods mods ce cx env (Attribute ann obj fld) es /\
  eval_expr cx (Attribute ann obj fld) (es with gas_obs := gs) = (INL tv,ee) /\
  compile_expr ce ty (Attribute ann obj fld) sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\ is_word_type ann /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx ann ann ee tv vv s /\ ptr_vv_ok cx ann tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) ann = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?v u Gf tf.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx (Attribute ann obj fld) es sa sb s0 ee v op u /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u) /\
    expr_store_bound cx ann v op u /\ ptr_val_ok cx ann v op Gf tf u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~u.vs_halted /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac compile_expr_extends >>
  drule_all_then assume_tac local_ptrs_reserved_next_var >>
  `copy_old_operand sm (vv_operand vv)` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[copy_old_operand_def]) >>
  drule_then strip_assume_tac compile_expr_attribute >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `LocatedValue ann psel` >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     simp[vv_holds_mods_def] >> IF_CASES_TAC >> simp[immutable_holds_mods_def] >>
     strip_tac >> (drule immutable_holds_read ORELSE drule reason_vv_read_success) >> simp[]) >>
  drule_all_then strip_assume_tac attribute_word_read_type >>
  `!v'. read_result cx tv ee = (INL v',ee) ==> value_has_type rt v'` by
    (rpt strip_tac >> `v' = v` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >> simp[]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[unwrap_value_def] >> disch_tac >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) attribute_word_load >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_ptr_load _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- fs[vv_location_def,vv_operand_def]) >>
  disch_then (qx_choosel_then [`rv`,`u`,`Gf`,`tf`] strip_assume_tac) >>
  `rv = v` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
  qpat_x_assum `rv = v` SUBST_ALL_TAC >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[expr_store_bound_word,ptr_val_ok_word] >>
  `u.vs_halted = s.vs_halted /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      conj_tac
      >- (irule attribute_word_read_post >> simp[] >>
          qexistsl [`s`,`sm`,`tv`,`LocatedValue ann psel`] >> simp[] >>
          qpat_assum `u.vs_inst_idx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
          first_assum ACCEPT_TAC) >>
      irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sm`,`tn`] >> simp[] >>
      rpt conj_tac >>
      qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])) >>
  simp[] >> conj_tac
  >- (`allocas_below_fmp u <=> allocas_below_fmp s` by
        (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
           (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
         simp[allocas_below_fmp_def]) >>
      asm_simp_tac bool_ss []) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]
QED
