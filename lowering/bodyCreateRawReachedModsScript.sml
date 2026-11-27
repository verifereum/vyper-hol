(* Typing and frame facts at the reached RawCreate bytecode operand. *)
Theory bodyCreateRawReachedMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyCopyReadPhysicalTypeMods bodyBopBytestringBindMods bodyImmutableCopyMemory
  exprBodyPreProps exprBodyPreTypingProps exprSimHyps exprSimConvertFromBytes
  exprPtrUnwrapStorageShape exprReasonOperand exprOperandVar stmtLoweringMono
  exprLoweringProps abiEncodeArgsCase abiValueEncoding exprSimProps exprSimWordArgs
  bodyMemoryDefs freshWrites loweringPosts vyperTypeArgFits vyperTypeSystem
  vyperStorageFootprint valueEncoding words arithmetic vyperArith
  compileEnv exprSimHypsDefs allocLimits vyperValue gasExplicitSites
  gasContext vyperState vyperAST context unitMemInv
Libs monadsyntax

Theorem raw_create_lowered_bytes[local]:
  expr_body_pre_mods mods ce cx env code es /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  bind (eval_expr cx code) (read_result cx) (es with gas_obs := obs) = (INL v,ee) ==>
  ?bs k. v = BytesV bs /\ lowered_value_type ce code = BaseT (BytesT (Dynamic k)) /\
    LENGTH bs <= k /\ k <= bound /\
    32 + LENGTH bs <= type_memory_bytes ce (lowered_value_type ce code) /\
    type_memory_bytes ce (lowered_value_type ce code) =
      type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    type_memory_bytes ce (lowered_value_type ce code) < 2 ** 64 /\
    type_memory_bytes ce (lowered_value_type ce code) < dimword (:256)
Proof
  strip_tac >>
  `~is_word_type (expr_type code)` by simp[is_word_type_def] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) copy_read_physical_type_gas_obs_mods >>
  qpat_x_assum `?pt rt. _` (qx_choosel_then [`pt`,`rt`] (map_every assume_tac o CONJUNCTS)) >>
  `arg_type_fits (lowered_value_type ce code) (expr_type code)` by
    (irule copy_lowered_fits_mods >>
     drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_then (irule_at Any) expr_body_pre_mods_inv >> simp[]) >>
  `?k. lowered_value_type ce code = BaseT (BytesT (Dynamic k)) /\ k <= bound` by
    (qpat_x_assum `arg_type_fits _ _` mp_tac >> simp[] >>
     Cases_on `lowered_value_type ce code` >> simp[arg_type_fits_def] >>
     rename1 `arg_type_fits (BaseT bt) _` >> Cases_on `bt` >> simp[arg_type_fits_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def]) >>
  `type_memory_bytes ce (lowered_value_type ce code) < 2 ** 64` by
    (`type_alloc_ok ce (expr_type code)` by
       (irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_mods_def]) >>
     drule_then (qspec_then `ce` assume_tac) (GEN_ALL (cj 1 abi_args_fits_memory_bytes)) >>
     gvs[type_alloc_ok_def,is_word_type_def] >> decide_tac) >>
  `rt = BaseTV (BytesT (Dynamic k))` by
    (irule evaluate_type_base_result >> qexists `get_tenv cx` >>
     qpat_assum `lowered_value_type ce code = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `rt = _` SUBST_ALL_TAC >>
  drule_then strip_assume_tac dynamic_bytes_value_typed >>
  qexistsl_tac [`bs`,`k`] >> simp[] >>
  conj_tac
  >- (simp[type_memory_size_def] >>
      qspec_then `k` mp_tac le_word_size_mul >> decide_tac) >>
  irule lt_dimword_256 >> qexists `64` >>
  gvs[]
QED

Theorem raw_create_located_tag[local]:
  vv_post_mods H ctx func ce cx code es sa a s ee raw vv t /\
  compile_expr ce (expr_type code) code sa = (vv,a) /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  type_memory_bytes ce (lowered_value_type ce code) = type_memory_size rt ==>
  vv_location vv <> SOME LocCalldata /\
  (!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
    vv_type vv = lowered_value_type ce code /\
    32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) =
      type_memory_bytes ce (lowered_value_type ce code))
Proof
  strip_tac >> Cases_on `vv` >> gvs[vv_location_def,vv_type_def] >>
  rename1 `LocatedValue tag p` >>
  `post_value_type ce code = expr_type code` by
    simp[post_value_type_bytestring,is_bytestring_type_def] >>
  `p.ptr_location <> LocCalldata /\
   (p.ptr_location <> LocMemory ==> tag = post_value_type ce code)` by
    (Cases_on `p.ptr_location` >>
     fs[vv_post_mods_def,vv_holds_mods_def,vv_holds_def]) >>
  simp[] >> disch_tac >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  gvs[body_immutable_copy_aligned_size]
QED

Theorem raw_create_operand_safe[local]:
  expr_body_pre_mods mods ce cx env code es /\
  compile_expr ce (expr_type code) code sa = (vv,a) /\ local_ptrs_reserved ce sa ==>
  (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\ (!l. vv_operand vv <> Label l)
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> disch_tac >> drule_all (cj 1 compiler_compile_var) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all compile_expr_reason_uniform >>
  disch_then (qspec_then `expr_type code` mp_tac) >>
  simp[reason_uniform_shape_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]
QED

Theorem raw_create_reached_frame[local]:
  vv_post_mods H ctx func ce cx code es sa a s ee raw vv t /\
  ghost_inv_at_mods D lo d ce cx ee G1 tn1 t /\
  ci_mono sa a /\ return_buf_frame d ce sa s /\ s.vs_alloca_next <= t.vs_alloca_next ==>
  wb_frame ce es ee sa s t /\ return_buf_frame d ce a t /\
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  simp_tac bool_ss [vv_post_mods_def,wb_frame_def] >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`sa`] >> fs[ci_mono_def]) >>
  fs[ghost_inv_at_mods_def]
QED

Theorem raw_create_reached_bytes_mods:
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env code es /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  compile_expr ce (expr_type code) code sa = (vv,a) /\
  local_ptrs_reserved ce sa /\ return_buf_frame d ce sa s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx code es sa a s ee raw vv t /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 t /\
    ghost_kept_at lo ce es sa G tn s G1 tn1 /\ s.vs_alloca_next <= t.vs_alloca_next) ==>
  ?bs k. v = BytesV bs /\ lowered_value_type ce code = BaseT (BytesT (Dynamic k)) /\
    LENGTH bs <= k /\ k <= bound /\
    32 + LENGTH bs <= type_memory_bytes ce (lowered_value_type ce code) /\
    type_memory_bytes ce (lowered_value_type ce code) =
      type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    type_memory_bytes ce (lowered_value_type ce code) < 2 ** 64 /\
    type_memory_bytes ce (lowered_value_type ce code) < dimword (:256) /\
    vv_location vv <> SOME LocCalldata /\
    (!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
      vv_type vv = lowered_value_type ce code /\
      32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) =
        type_memory_bytes ce (lowered_value_type ce code)) /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods ce cx env ee /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
    ci_mono sa a /\ local_ptrs_reserved ce a /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\ (!l. vv_operand vv <> Label l) /\
    wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G1 tn1 /\
    return_buf_frame d ce a t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 t)
Proof
  strip_tac >>
  drule_all_then (qspec_then `st0` (map_every assume_tac o CONJUNCTS))
    bop_bytestring_operand_source_mods >>
  drule_all_then strip_assume_tac raw_create_lowered_bytes >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `ci_mono sa a` by
    (qspecl_then [`ce`,`expr_type code`,`code`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  drule_all_then strip_assume_tac raw_create_reached_frame >>
  drule_all_then strip_assume_tac raw_create_located_tag >>
  drule_all_then strip_assume_tac raw_create_operand_safe >>
  qexistsl_tac [`bs`,`k`] >> simp[] >>
  conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[vv_post_mods_def]
QED
