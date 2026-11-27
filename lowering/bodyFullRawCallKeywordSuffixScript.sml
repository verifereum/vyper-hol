(* Full evaluation from the forced bytes value through the keyword list. *)
Theory bodyFullRawCallKeywordSuffix
Ancestors
  bodyFullShadowBodyInv bodyFullPreds bodySimFull bodyFullWordArgs
  bodyFullIfExpReach stateRelProj bodyFullRawCallHeader bodyFullHashKeccakFixed
  bodyFullRawCallGeneratedPrefix gasOutcomeFullCompose gasOutcomeFullGuarded
  exprSimRawCall exprSimSource wordArgsPtr gasShadowCompileStmtHelpers
  gasShadowState representationCleanPtr gasExemptCert bodyMemoryDefs
  exprLoweringProps exprSimWordArgs fragExec list gasShadow vyperStorageTrace
  loweringPosts
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

Theorem raw_call_forced_data_kwargs_full_from_action:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env esD /\
  expr_sim_inv_mods mods cenv cx env esD /\ body_exprs_full_ok_mods mods exps cx kws /\
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  expr_type d = BaseT (BytesT (Dynamic cap)) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\ emit_op ADD [data; Lit 32w] s3 = (dp,s4) /\
  lower_word_args cenv (K (BaseT (UintT 256))) kws s4 = (xs,s5) /\
  lower_word_args (gas_shadow_env T cenv) (K (BaseT (UintT 256)))
    (MAP gas_shadow_expr kws) h4 = (xs,h5) /\
  gas_shadow_state s4 h4 /\ gas_shadow_state s5 h5 /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code s2 s4 func /\ fn_has_code s4 s5 func /\ fn_has_code h4 h5 shadow_func /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame dframe cenv sa s0 /\
  storage_trace_domain cx st0 esD.storage_trace /\
  (!fn inst u. frag_reachable ctx func tD fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H esD.storage_trace ==>
    expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    s0.vs_alloca_next <= tA.vs_alloca_next /\
    expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
    tD.vs_current_bb = s2.cs_current_bb /\
    tD.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func tD /\
    tA.vs_alloca_next <= tD.vs_alloca_next /\
    ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD /\
    ptr_val_ok cx (post_value_type cenv d) (BytesV bs) data GD tnD tD /\ ~tD.vs_halted) /\
  (!v. storage_trace_frame (next v)) /\
  (!H exc ee gt r. expr_exit (INR exc) r /\
     halt_exit H cx ee (INR exc) r ==> R H (INR exc) ee gt r) /\
  (!b x l p base extent t4 G4 tn4 marks kvs esK tk GK tnK.
    data = Var x /\ len = Var l /\ dp = Var p /\
    (!z. data = Var z ==> not_fresh_at s2 z) /\
    (!z. len = Var z \/ dp = Var z ==> not_fresh_at s4 z) /\
    eval_operand data tD = SOME (n2w b) /\ b < dimword (:256) /\
    b+32+LENGTH bs < dimword (:256) /\
    post_value_type cenv d = expr_type d /\
    evaluate_type (get_tenv cx) (post_value_type cenv d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_var <= s2.cs_next_var /\
    local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s4 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
    eval_operand len t4 = SOME (n2w (LENGTH bs)) /\ eval_operand dp t4 = SOME (n2w (b+32)) /\
    op_taint tn4 len = {} /\ op_taint tn4 dp = {} /\ op_prov G4 len = NONE /\
    FLOOKUP G4 p = SOME (base,extent) /\ base <= b /\ b+32+LENGTH bs <= base+extent /\
    (!mem. mem_agree_outside tn4.t_mem t4.vs_memory mem ==>
      mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
    (!z. not_fresh_at s2 z ==> lookup_var z t4 = lookup_var z tD /\
      FLOOKUP G4 z = FLOOKUP GD z /\ op_taint tn4 (Var z) = op_taint tnD (Var z)) /\
    t4.vs_allocas = tD.vs_allocas /\ t4.vs_alloca_next = tD.vs_alloca_next /\
    (!sa es0 s0 G0 tn0. sa.cs_next_var <= s2.cs_next_var /\
      ghost_kept_at lo cenv es0 sa G0 tn0 s0 GD tnD ==>
      ghost_kept_at lo cenv es0 sa G0 tn0 s0 G4 tn4) /\
    (!sa es0 s0. sa.cs_next_var <= s2.cs_next_var /\ wb_frame cenv es0 esD sa s0 tD ==>
      wb_frame cenv es0 esD sa s0 t4) /\
    (!e ee. MEM e kws /\ expr_sim_inv_mods mods cenv cx env ee ==>
      expr_body_pre_mods mods cenv cx env e ee /\ is_word_type (expr_type e)) /\
    (!tail. eval_exprs cx kws (esD with gas_obs := gas_explicit marks t4.vs_gas_readings ++ tail) =
      (INL kvs,esK with gas_obs := tail)) /\
    storage_trace_domain cx st0 esK.storage_trace /\ esK.gas_obs = [] /\
    (!H. valid_horizon cx st0 H esK.storage_trace ==>
      typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
      stmt_state_rel H ctx func cenv cx esK tk /\ storage_well_formed_on cx esK (FST H) /\
      ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk) /\
    ~tk.vs_halted /\ tk.vs_current_bb = s5.cs_current_bb /\
    tk.vs_inst_idx = LENGTH s5.cs_current_insts /\ alloca_history func tk /\
    t4.vs_alloca_next <= tk.vs_alloca_next /\ ghost_kept_at lo cenv esD s4 G4 tn4 t4 GK tnK /\
    EVERY (\x. op_taint tnK x = {}) xs ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (next kvs) (esK,tk,GK,tnK) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx kws) next) (esD,tD,GD,tnD) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   sa.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s4.cs_next_var` by
    (rpt (qhdtm_x_assum `ci_mono` (mp_tac o REWRITE_RULE [ci_mono_def])) >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s4` by
    metis_tac[local_ptrs_reserved_next_var,arithmeticTheory.LESS_EQ_TRANS] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ ctx func cenv cx a es sa s1 s0 esA av addr tA`
       (assume_tac o MATCH_MP expr_post_frame) >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `return_buf_frame dframe cenv s2 tD` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv s1 tA` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def]) >>
     simp[NoAsms] >> strip_tac >> simp[]) >>
  `post_value_type cenv d = expr_type d` by
    (irule post_value_type_bytestring >> simp[compileEnvTheory.is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv d) =
     SOME (BaseTV (BytesT (Dynamic cap))) /\ ~is_word_type (post_value_type cenv d)` by
    (`expr_body_pre cenv cx env d esD` by
       (irule expr_body_pre_raw_call_arg >>
        first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     drule_at (Pat `expr_body_pre _ _ _ d _`) exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def,compileEnvTheory.is_word_type_def]) >>
  `stmt_state_rel (storage_trace_horizon esD.storage_trace) ctx func cenv cx esD tD /\
   expr_val_rel cx (post_value_type cenv d) (BytesV bs) data tD` by
    (qpat_assum `expr_post _ _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def,NoAsms]) >>
  suspend "header"
QED

Resume raw_call_forced_data_kwargs_full_from_action[header]:
  `?b. eval_operand data tD = SOME (n2w b) /\ b+32+LENGTH bs < dimword (:256) /\
       mem_word_at b tD.vs_memory = n2w (LENGTH bs)` by
    (qpat_assum `expr_val_rel cx _ _ data tD` mp_tac >>
     qpat_assum `expr_store_bound cx _ _ data tD` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ esD tD` (mp_tac o MATCH_MP stmt_state_rel_alloca_room) >>
     qpat_assum `evaluate_type _ _ = SOME (BaseTV (BytesT (Dynamic cap)))` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv d)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_val_rel_def,exprSimMemDefsTheory.expr_store_bound_def,alloca_room_def] >>
     rpt strip_tac >> qexists_tac `w2n w` >>
     gvs[exprSimPropsTheory.val_store_size_def,valueEncodingDefsTheory.val_in_memory_def] >>
     qspec_then `LENGTH bs` assume_tac exprSimPropsTheory.le_word_size_mul >> decide_tac) >>
  `b < dimword (:256)` by decide_tac >>
  `!z. data = Var z ==> not_fresh_at s2 z` by
    (qpat_assum `lower_value compile_expr cenv (expr_type d) d s1 = _` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv s1` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  drule_all exprSimHashTheory.hash_data_prefix_run >> strip_tac >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `allocas_from lo tD /\ lo <= tD.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ esD GD tnD tD`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp tD` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  drule_all raw_call_header_joint >>
  disch_then (qspecl_then [`PG`,`esD`,`gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  disch_then (qx_choose_then `t4` strip_assume_tac) >>
  irule (Q.INST [`n` |-> `0`] raw_call_generated_prefix_full) >>
  conj_tac >- (irule storage_trace_frame_bind_all >> simp[cj 6 evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G4`,`t4`,`tn4`] >> conj_tac
  >- (simp[NoAsms] >> rpt strip_tac >> first_assum irule) >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esD t4 /\
    storage_well_formed_on cx esD (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esD G4 tn4 t4` by
    (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _` mp_tac >>
     qpat_assum `!H D d. stmt_state_rel _ _ _ _ _ _ tD /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> first_x_assum drule >>
     simp[expr_post_def] >> metis_tac[]) >>
  `return_buf_frame dframe cenv s4 t4` by
    (qpat_assum `!sa d. _ ==> _ /\ return_buf_frame _ _ _ t4`
       (qspecl_then [`s2`,`dframe`] mp_tac) >> simp[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst u. frag_reachable ctx func t4 fn inst u ==> dalloca_fmp_headroom inst u` by
    metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t4` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
    expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[compileEnvTheory.is_word_type_def]) >>
  suspend "keywords"
QED

Resume raw_call_forced_data_kwargs_full_from_action[keywords]:
  qpat_assum `lower_word_args cenv (K _) kws s4 = _`
    (assume_tac o SIMP_RULE std_ss [combinTheory.K_DEF]) >>
  qpat_assum `lower_word_args _ (K _) (MAP gas_shadow_expr kws) h4 = _`
    (assume_tac o SIMP_RULE std_ss [combinTheory.K_DEF]) >>
  qspecl_then [`kws`,`DF`,`lo`,`dframe`,`ctx`,`shadow_ctx`,`PG`,`tops`,
     `func`,`shadow_func`,`cenv`,`env`,`cx`,`BaseT (UintT 256)`,
     `esD`,`st0`,`s4`,`s5`,`h4`,`h5`,`xs`,`t4`,`G4`,`tn4`] mp_tac
    lower_word_args_sim_full >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ kwQ kwR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[cj 6 evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- first_assum ACCEPT_TAC >>
  qexists_tac `\H rr ee G tn t. kwQ H rr ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ kwQ kwR` (irule_at Any) >>
      simp[Abbr `kwR`,NoAsms] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      Cases_on `res` >> gvs[wb_args_exit_def] >> first_x_assum irule >>
      gvs[stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marks`,`resK`,`esK`,`GK`,`tnK`,`tk`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esK.storage_trace) esK.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qunabbrev_tac `kwQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _`
    (qspec_then `storage_trace_horizon esK.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `resK = INL _` SUBST_ALL_TAC >>
  rename1 `typed_args_post _ _ _ _ _ _ _ _ esK _ _ kvs tk` >>
  `!H. valid_horizon cx st0 H esK.storage_trace ==>
    typed_args_post H ctx func cenv cx esD s4 t4 esK kws xs kvs tk /\
    stmt_state_rel H ctx func cenv cx esK tk /\ storage_well_formed_on cx esK (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esK GK tnK tk` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> _` drule >>
     simp[exprSimPrecompilesTheory.typed_args_post_def,NoAsms]) >>
  disj1_tac >> qexists_tac `kvs` >> simp[] >>
  qpat_assum `!b x l p base extent t4 G4 tn4 marks kvs esK tk GK tnK.
    _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  rename1 `FLOOKUP G4 px = SOME (header_base,header_extent)` >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (qpat_assum `data = Var _` mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[])
  >- (qpat_assum `len = Var _` mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qexistsl_tac [`G4`,`b`,`header_base`,`header_extent`,`marks`,`px`,`t4`,`tn4`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_call_forced_data_kwargs_full_from_action
