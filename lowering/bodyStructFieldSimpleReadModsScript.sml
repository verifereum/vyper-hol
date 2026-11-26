(* Read-only unwrap of the reached StructLit field, after its destination ADD. *)
Theory bodyStructFieldSimpleReadMods
Ancestors arithmetic[qualified,ignore_grammar]
  bodyStructFieldCutsMods bodyIfExpWordReadMods bodyIfExpArmUnwrapMods
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullStructLitInputs
  bodyPtrSignedConvertSourceFrame exprSimWordArgs wordArgsPtr
  bodyCopyReadPhysicalTypeMods exprOperandVar exprSimUnwrap fragGasOriginPtrDead
  exprSimFullBundleProps stateRelProj valueEncodingTyping
  exprLowering compileEnv bodyFullPostsMods loweringPosts bodyPtrDefs
  fragGasOriginPtr context exprSimProps loweringStateRelDefs loweringShapeDefs
  allocaSiteResource exprSimAggregateChildren finite_map pred_set words list pair
  bodySimStmtFacts bodyWriteSubscriptSourceMods bodyFullHashKeccakFixed
  typedCopyCompatibility exprSimLayoutTransport vyperTypeArgFits
  exprSimCopy vyperStorageFootprint exprLoweringProps typedMemoryCopy vyperTypeSystem

val empty_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                      d_imm := K {}; d_ret := K {}|>``;

val readonly = ``
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (Gf:string |-> num # num) x = FLOOKUP (G:string |-> num # num) x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

val word_result = ``
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    u.vs_current_bb = su.cs_current_bb /\ u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ ^readonly``;

Theorem struct_field_word_run[local]:
  unwrap_value ce vv sn = (op,su) /\ fn_has_code sn su func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sn /\
  copy_old_operand sn (vv_operand vv) /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v u Gf tf. ^word_result
Proof
  strip_tac >> Cases_on `vv`
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def, comp_return_def] >> strip_tac >> gvs[] >>
      qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
      qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
      simp[vv_holds_mods_def,vv_holds_def,expr_val_rel_def] >> strip_tac >>
      qexistsl [`v`,`s`,`G`,`tn`] >>
      fs[ptr_vv_ok_def, ptr_val_ok_def, cj 1 gas_origin_ptr_path_rules]) >>
  rename1 `LocatedValue tag p` >>
  drule word_arm_location >> simp[] >> strip_tac >>
  qpat_x_assum `tag = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def] >> disch_tac >>
  qpat_assum `ghost_inv_at_mods Dh _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^empty_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`su`,`rt`,`op`,`PG`] mp_tac) >>
  impl_tac >- gvs[vv_location_def, vv_operand_def, arithmeticTheory.ADD_COMM] >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

Theorem struct_field_word_post[local]:
  vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv s /\
  local_ptrs_reserved ce sn /\ si.cs_next_var <= sn.cs_next_var /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x s) ==>
  expr_post_mods H ctx func ce cx e es si su s0 ee v op u
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sn`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sn`] >> simp[]) >>
  `!x. not_fresh_at si x ==> lookup_var x u = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  simp[expr_post_mods_def, expr_post_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

Theorem struct_field_readonly_prefix[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gi,ti)
    (root,addr,capacity,aid) (H,D,ee,sn,G,tn,s) cells off /\
  local_ptrs_reserved ce sn /\ sn.cs_next_var <= su.cs_next_var /\
  sn.cs_next_id <= su.cs_next_id /\ ^readonly /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sn x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sn x) /\
  u.vs_current_bb = su.cs_current_bb /\ u.vs_inst_idx = LENGTH su.cs_current_insts /\
  alloca_history func u ==>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gi,ti)
    (root,addr,capacity,aid) (H,D,ee,su,Gf,tf,u) cells off
Proof
  simp[struct_prefix_mods_def, expr_sim_full_endpoint_def] >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
   u.vs_halted = s.vs_halted` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `!n p k. local_region ce ee.scopes u n p k <=> local_region ce ee.scopes s n p k` by
    (rpt gen_tac >> irule local_region_lookup_cong >> simp[] >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x cap. not_fresh_at sn x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x u cap` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sn`] >> simp[])
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sn`] >> simp[])
  >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sn`,`tn`] >> simp[])
  >- (irule wb_frame_readonly_tail >> qexistsl [`sn`,`s`] >> simp[])
  >- (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
      rpt strip_tac >> `not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >> simp[])
  >- metis_tac[not_fresh_at_mono]
  >- (rpt strip_tac >> qpat_assum `!n p k. local_region ce ee.scopes s n p k ==> _` drule >> simp[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- fs[bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_ok_def]
  >> strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> simp[]
QED

(* The destination is already live before the read. Its bound within the
   result allocation also bounds it by the machine's allocation frontier. *)
Theorem struct_field_read_destination[local]:
  struct_prefix_mods frame anchor (root,addr,capacity,aid)
    (H,D,ee,su,Gf,tf,u) cells off /\
  off + type_memory_size dtv <= capacity ==>
  addr + off + type_memory_size dtv < dimword (:256) /\
  addr + off + type_memory_size dtv <= u.vs_alloca_next
Proof
  PairCases_on `frame` >> PairCases_on `anchor` >>
  simp[struct_prefix_mods_def] >> strip_tac >>
  `addr + capacity <= u.vs_alloca_next` by
    (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     drule_all alloca_site_registered_below >> simp[]) >>
  decide_tac
QED

Theorem struct_field_read_disjoint[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) anchor (root,addr,capacity,aid)
    (H,D,ee,su,Gf,tf,u) cells off /\ aid < si.cs_next_id /\
  off + type_memory_size dtv <= capacity /\
  expr_val_at ce cx sty si su ee v op u /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  ~is_bytestring_type sty /\ 0 < type_memory_size stv /\
  eval_operand op u = SOME sw ==>
  w2n sw + val_footprint stv v <= addr + off \/
  addr + off + type_memory_size dtv <= w2n sw
Proof
  PairCases_on `anchor` >> simp[struct_prefix_mods_def] >> strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) structlit_physical_footprint_bounds >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (qspecl_then [`sw`, `addr + off`, `type_memory_size dtv`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_assum `!name p k. local_region ce ee.scopes u name p k ==> _` drule >>
    disch_tac >> decide_tac) >> simp[]
QED

val field_entry = ``
  compile_expr ce ty e si = (vv,sm) /\ unwrap_value ce vv sn = (op,su) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn su func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce si /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e es si sn s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (expr_type e) ==> ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
     ~is_word_type (expr_type e) ==> ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es si G0 tn0 s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func s``;

val identity_vv = ``(?tag x. vv = StackValue tag x) \/
  (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\ ~is_word_type tag)``;

val physical = ``
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ op_taint tf op = {} /\
    (is_word_type (expr_type e) ==>
       eval_operand op u = SOME (typed_val_to_w256 stv v)) /\
    (~is_word_type (expr_type e) ==>
       ?sw. eval_operand op u = SOME sw /\
         w2n sw + type_memory_size stv < dimword (:256) /\
         (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
             val_in_memory stv v (w2n sw) m) /\
         (0 < type_memory_size stv ==>
           w2n sw + type_memory_size stv <= u.vs_alloca_next /\
           ?src. op = Var src /\ not_fresh_at su src /\
             ptr_covers Gf tf src u (type_memory_size stv))) /\
    (~is_word_type (expr_type e) /\ ~is_bytestring_type (lowered_value_type ce e) ==>
       post_value_type ce e = lowered_value_type ce e)``;

val field_read = ``
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func ce cx e es si su s0 ee v op u) /\
    ^physical /\ ^readonly /\
    u.vs_current_bb = su.cs_current_bb /\ u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u``;

Theorem struct_field_nonword_run[local]:
  ^field_entry /\ ~is_word_type (expr_type e) /\ (^identity_vv) ==>
  ?v u Gf tf stv. ^field_read
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `su = sn` by
    (qpat_x_assum `^identity_vv` strip_assume_tac >> fs[unwrap_value_def,comp_return_def]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) ifexp_arm_nonword_unwrap_mods >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`st0`,`explicit`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`v`,`u`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  `u = s /\ Gf = G /\ tf = tn` by
    (qpat_x_assum `(su = sn /\ _) \/ _` mp_tac >> simp[] >> strip_tac >> fs[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `~is_bytestring_type (lowered_value_type ce e) ==>
   post_value_type ce e = lowered_value_type ce e` by
    (strip_tac >> drule_all copy_read_physical_type_gas_obs_mods >> simp[]) >>
  `u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by
    simp[venomStateTheory.venom_state_component_equality] >>
  qexistsl [`v`,`u`,`Gf`,`tf`,`rt`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      drule >> simp[]) >>
  conj_tac >- (
    simp[] >>
    qpat_assum `type_memory_size rt = 0 \/ _` strip_assume_tac >>
    fs[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  simp[]
QED

Theorem struct_field_word_value_type[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt ==>
  !v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v
Proof
  strip_tac >> gen_tac >> disch_tac >>
  `(do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`) expr_body_pre_eval_mods >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ (es with gas_obs := gs)`)) >>
  strip_tac >>
  drule exprBodyPrePropsTheory.expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP
    (SPEC_ALL vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv)) >>
  fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> gvs[]
QED

Theorem struct_field_word_read[local]:
  ^field_entry /\ is_word_type (expr_type e) /\
  lowered_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  local_ptrs_reserved ce sn /\ si.cs_next_var <= sn.cs_next_var ==>
  ?v u Gf tf stv. ^field_read
Proof
  strip_tac >>
  `copy_old_operand sn (vv_operand vv)` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[copy_old_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v` by
    (gen_tac >> disch_tac >> drule_all struct_field_word_value_type >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) struct_field_word_run >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type _) = _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `value_has_type rt v` by (qpat_assum `!v. read_result _ _ _ = _ ==> _` irule >> simp[]) >>
  qexistsl [`v`,`u`,`Gf`,`tf`,`rt`] >>
  conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
    `!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x s` by
      (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` drule >> simp[]) >>
    irule struct_field_word_post >> simp[] >>
    qexistsl [`s`,`sn`,`tv`,`vv`] >> simp[] >>
    qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
    qpat_x_assum `u.vs_inst_idx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
    simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  simp[]
QED

val prefix_at = ``struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gi,ti)
  (root,addr,capacity,aid) (H,(DF : ((bool # 256 word # type_value) list # num list) -> dead) H,ee,sn,G,tn,s) cells off``;
val prefix_done = ``struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gi,ti)
  (root,addr,capacity,aid) (H,(DF : ((bool # 256 word # type_value) list # num list) -> dead) H,ee,su,Gf,tf,u) cells off``;

Theorem struct_field_widen_word[local]:
  type_widens_to tenv sty dty ==> (is_word_type sty <=> is_word_type dty)
Proof
  rw[type_widens_to_def] >> metis_tac[compatible_word_type]
QED

Theorem struct_field_operand_after_read[local]:
  ^physical /\ ^prefix_done /\ aid < si.cs_next_id /\
  expr_post_mods H ctx func ce cx e es si su s0 ee v op u /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  off + type_memory_size dtv <= capacity /\ not_fresh_at su dst /\
  lookup_var dst u = SOME (n2w (addr + off)) /\
  ptr_covers Gf tf dst u (type_memory_size dtv) ==>
  struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,dty,stv,dtv)
    (op,v) (dst,addr + off) (su,Gf,tf,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) dty` by
    metis_tac[type_widens_to_trans] >>
  `is_word_type (expr_type e) <=> is_word_type dty` by
    (qpat_assum `type_widens_to _ (expr_type e) dty` (mp_tac o MATCH_MP struct_field_widen_word) >> simp[]) >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `addr + off + type_memory_size dtv < dimword (:256) /\
   addr + off + type_memory_size dtv <= u.vs_alloca_next` by
    (drule_all struct_field_read_destination >> simp[]) >>
  simp[struct_operand_mods_def, value_has_type_val_wf] >>
  Cases_on `is_word_type dty`
  >- (`expr_type e = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
      `lowered_value_type ce e = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
      `stv = dtv` by metis_tac[optionTheory.SOME_11] >> fs[]) >>
  `~is_word_type (expr_type e)` by fs[] >>
  qpat_x_assum `~is_word_type (expr_type e) ==> ?sw. _` (drule_then strip_assume_tac) >>
  simp[] >> disch_tac >>
  qpat_x_assum `0 < type_memory_size stv ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- decide_tac >> strip_tac >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  `~is_bytestring_type (lowered_value_type ce e)` by metis_tac[type_widens_from_bytestring] >>
  `~is_word_type (lowered_value_type ce e)` by
    (qpat_assum `type_widens_to _ (lowered_value_type ce e) (expr_type e)`
     (mp_tac o MATCH_MP struct_field_widen_word) >> simp[]) >>
  `post_value_type ce e = lowered_value_type ce e` by simp[] >>
  `expr_val_at ce cx (lowered_value_type ce e) si su ee v op u` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     metis_tac[]) >>
  drule_all struct_field_read_disjoint >> simp[]
QED

Theorem struct_field_simple_run[local]:
  ^field_entry /\ (is_word_type (expr_type e) \/ (^identity_vv)) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  local_ptrs_reserved ce sn /\ si.cs_next_var <= sn.cs_next_var ==>
  ?v u Gf tf stv. ^field_read
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (expr_type e)`
     >- (`is_word_type dty` by
           (qpat_assum `type_widens_to _ (expr_type e) dty`
              (mp_tac o MATCH_MP struct_field_widen_word) >> simp[]) >>
         `expr_type e = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
         `lowered_value_type ce e = expr_type e` by metis_tac[compileEnvTheory.type_widens_to_word] >>
         drule_at (Pat `unwrap_value _ _ _ = _`) struct_field_word_read >>
         disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
         disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
         disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
         disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
         disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
         disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
         disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
         disch_then (qspecl_then [`dtv`,`explicit`,`d`,`ctx`,`PG`,`DF`] mp_tac) >> simp[]) >>
     drule_at (Pat `unwrap_value _ _ _ = _`) struct_field_nonword_run >>
     disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
     disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
     disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     disch_then (qspecl_then [`explicit`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
     `^identity_vv` by fs[] >> simp[]
QED

Theorem struct_field_readonly_tail[local]:
  ^readonly /\ ~s.vs_halted ==>
  wb_frame ce ee ee sn s u /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
  u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  conj_tac
  >- (irule wb_frame_readonly_tail >> qexistsl [`sn`,`s`] >>
      simp[wb_frame_refl] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` drule >> simp[]) >>
  simp[] >> irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >>
  simp[ghost_kept_at_refl] >> rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` drule >> simp[]
QED

Theorem struct_field_simple_read_mods:
  ^field_entry /\ (is_word_type (expr_type e) \/ (^identity_vv)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ^prefix_at) /\
  aid < si.cs_next_id /\ off + type_memory_size dtv <= capacity /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  type_widens_to (get_tenv cx) (expr_type e) dty /\
  not_fresh_at sn dst /\ lookup_var dst s = SOME (n2w (addr + off)) /\
  ptr_covers G tn dst s (type_memory_size dtv) ==>
  ?v u Gf tf stv. ^field_read /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ^prefix_done) /\
    wb_frame ce ee ee sn s u /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\ cs_extends sn su /\
    struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,dty,stv,dtv)
      (op,v) (dst,addr + off) (su,Gf,tf,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `si.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) struct_field_simple_run >>
  `ci_mono sn su` by (qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  qpat_x_assum `ci_mono sn su` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `si` >> simp[]) >>
  `!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `si` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ^prefix_done` by
    (gen_tac >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_at (Pat `struct_prefix_mods _ _ _ _ _ _`) struct_field_readonly_prefix >>
     disch_then (qspecl_then [`u`,`tf`,`su`,`Gf`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qexistsl [`v`,`u`,`Gf`,`tf`,`stv`] >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then strip_assume_tac struct_field_readonly_tail >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  `not_fresh_at su dst` by metis_tac[not_fresh_at_mono] >>
  `lookup_var dst u = SOME (n2w (addr + off)) /\ ptr_covers Gf tf dst u (type_memory_size dtv)` by
    (qpat_assum `!x. not_fresh_at sn x ==> _ /\ _ /\ _` (qspec_then `dst` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> conj_tac >- simp[] >>
     drule_all exprPtrUnwrapFramesTheory.copy_ptr_covers_transport >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_all struct_field_operand_after_read >> simp[]
QED
