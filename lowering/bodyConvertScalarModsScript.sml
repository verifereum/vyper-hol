(* Scalar Convert: a forced linked operand and a read-only conversion suffix. *)
Theory bodyConvertScalarMods
Ancestors
  bodyTypeBuiltinAbiMods bodyFullConvertScalarSuffix bodyScalarStackVVMods
  bodyConvertScalarOpcode bodyConvertScalarAbortKind bodyConvertScalarRevertOrigin
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPathHistory
  bodyPtrTypeBuiltinsScalarSemantic bodySimStmtFacts exprBodyPreTypingProps
  exprSimFullBundleProps exprOperandVar gasShadowCompileStmtHelpers
  exprBodyPreProps exprSimHypsDefs exprSafeOperand exprSimSource
  vyperTypeSystem vyperTypeEvalCaseProofs vyperTypeExtCallCore vyperTypeExprSoundness
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods haltExitProj
  bodyForcedStorageFrameMods bodyWriteSubscriptSourceMods
  exprBopLowering externalEntryShape exprSimHyps exprSimStack exprSimConvert
  exprLowering exprLoweringProps compileEnv vyperContext vyperInterpreter
  vyperState vyperAST gasShadow gasShadowState fragExec
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs loweringPosts
  exprSimWordArgs exprSimProps assignTuplePtrLoadStep stateFrame allocasBelowFmpUpdatesProps
  loweringStateRelDefs freshWrites venomState ptrDiscipline exprSimMemDefs
  vyperStorageFootprint gasContext gasStorage gasSummary fragGasOriginPtr
  exprSimDefs bodyFullPredsMods vyperStorageTrace stmtSimProps
Libs monadsyntax

Theorem convert_scalar_pre[local]:
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  ~is_bytestring_type (expr_type e) ==>
  ann = dst /\ valid_conversion (expr_type e) dst /\
  expr_body_pre_mods mods cenv cx env e es /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  IS_SOME (evaluate_type (get_tenv cx) dst) /\
  is_word_type (expr_type e) /\ is_word_type dst /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
       cenv.ce_flag_n_members (nsid_to_string name) = n)
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule type_builtin_body_arg_pre_mods >>
     conj_tac >- (drule expr_body_pre_mods_inv >> simp[]) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
       (irule_at Any) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  simp[Once well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_result_ok_def] >> strip_tac >> gvs[] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `well_formed_type env.type_defs (expr_type e)` by
    (irule well_typed_expr_type_well_formed >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule expr_body_pre_mods_well_typed >>
     qpat_assum `expr_body_pre_mods _ _ _ _ e _` (irule_at Any)) >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    (qpat_assum `well_formed_type env.type_defs (expr_type e)` mp_tac >>
     qpat_assum `env.type_defs = get_tenv cx` (fn th => PURE_REWRITE_TAC[th]) >>
     simp[well_formed_type_def]) >>
  fs[well_formed_type_def] >>
  drule_all scalar_source_word_types >> simp[] >> strip_tac >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def]
QED

Theorem convert_scalar_compile_cut[local]:
  ~is_bytestring_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm = (out,sb) ==>
  compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa =
    (StackValue dst out,sb)
Proof
  strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  Cases_on `dst` >> gvs[exprBopLoweringTheory.as_stack_val_pair]
QED

Theorem convert_scalar_source[local]:
  bind (eval_expr cx (TypeBuiltin dst Convert dst [e])) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (convert_result cx (expr_type e) dst v,ee))
Proof
  simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  rename1 `eval_expr cx e st = (INL raw,ee)` >>
  Cases_on `read_result cx raw ee` >> Cases_on `q` >> simp[] >>
  rename1 `read_result cx raw ee = (INL v,mid)` >>
  simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) v dst` >>
  simp[read_result_def, return_def, raise_def]
QED

Theorem convert_scalar_cuts[local]:
  ~is_bytestring_type (expr_type e) /\
  compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?x sm shm out.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) sha = (x,shm) /\
    compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm = (out,sb) /\
    vv = StackValue dst out /\ gas_shadow_state sm shm /\
    sa.cs_next_var <= sm.cs_next_var /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  Cases_on `compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm` >>
  drule_all_then assume_tac convert_scalar_compile_cut >> gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) sha` >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `gas_shadow_state sm shm` >>
  qmatch_assum_rename_tac `lower_value compile_expr cenv _ e sa = (x,sm)` >>
  Cases_on `compile_type_convert x (case dst of FlagT name =>
       ConvToFlag ((gas_shadow_env T cenv).ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type (gas_shadow_expr e)) dst) shm` >>
  rename1 `compile_type_convert x _ shm = (sv,shb')` >>
  `compile_expr (gas_shadow_env T cenv) ty
      (TypeBuiltin dst Convert dst [gas_shadow_expr e]) sha = (StackValue dst sv,shb')` by
    (irule convert_scalar_compile_cut >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ cs_extends sha shm` by
    metis_tac[compile_expr_grows] >>
  qmatch_assum_rename_tac `fn_has_code sa sb func` >>
  `cs_extends sm sb /\ cs_extends shm shb` by
    metis_tac[cj 1 compile_type_convert_labels,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

Theorem convert_scalar_landing[local]:
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
  ghost_inv_at_mods D lo d cenv cx mid G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  is_word_type dst /\ evaluate_type (get_tenv cx) dst = SOME rt /\
  eval_operand out u = SOME (typed_val_to_w256 rt w) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
  (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z t /\
    FLOOKUP Gu z = FLOOKUP G z /\ op_taint tnu (Var z) = op_taint tn (Var z)) /\
  tnu.t_mem = tn.t_mem /\ tnu.t_stor = tn.t_stor /\
  tnu.t_trans = tn.t_trans /\ tnu.t_imm = tn.t_imm /\
  op_prov Gu out = NONE /\ op_taint tnu out = {} ==>
  expr_post_mods H ctx func cenv cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 mid w out u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods D lo d cenv cx mid Gu tnu u /\
  ptr_val_ok cx dst w out Gu tnu u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu
Proof
  strip_tac >>
  `u = (t with vs_inst_idx := u.vs_inst_idx) with vs_vars := u.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  `u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_call_ctx = t.vs_call_ctx /\ u.vs_accounts = t.vs_accounts /\
   u.vs_transient = t.vs_transient /\ u.vs_immutables = t.vs_immutables` by
    (pop_assum (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     simp[allocas_below_fmp_updates]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  fs[expr_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     qexistsl_tac [`t`,`sm`] >> simp[] >> drule expr_post_state >> simp[]) >>
  simp[ptr_val_ok_word] >> rpt conj_tac
  >- suspend "ordinary"
  >- (irule immutable_frame_mods_exterior_frame >>
      qpat_assum `immutable_frame_mods _ _ _ mid t` (irule_at Any) >>
      qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >> simp[])
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qpat_assum `ghost_inv_at_mods _ _ _ _ _ mid G tn t` (irule_at Any) >>
      qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >> simp[]) >>
  irule ghost_kept_at_clean_suffix >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ G tn` (irule_at Any) >> simp[]
QED

Resume convert_scalar_landing[ordinary]:
  qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  simp[expr_post_def, expr_type_def, expr_val_rel_def, expr_val_at_def] >>
  `locals_kept cenv es mid s0 u` by
    (irule locals_kept_mem_tail >> qexists_tac `t` >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> conj_tac
      >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[]) >>
  `pure_frame cenv func es sa s0 u <=> pure_frame cenv func es sa s0 t` by
    (irule pure_frame_state_cong >> simp[]) >>
  fs[] >> metis_tac[]
QED
Finalise convert_scalar_landing

val scalar_convert_post = ``\H (res:value + exception) ee Gf tnf u. ?w. res = INL w /\
  expr_post_mods H ctx func cenv cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 ee w out u /\
  expr_store_bound cx dst w out u /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx ee Gf tnf u /\
  ptr_val_ok cx dst w out Gf tnf u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf``;

val scalar_convert_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res:value + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem convert_scalar_suffix[local]:
  valid_conversion (expr_type e) dst /\ ~is_bytestring_type (expr_type e) /\
  is_word_type (expr_type e) /\ is_word_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  ~t.vs_halted /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    ptr_val_ok cx (expr_type e) v x G tn t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (\ee. (convert_result cx (expr_type e) dst v,ee)) (mid,t,G,tn)
    ^scalar_convert_post ^scalar_convert_exit
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o SRULE [expr_post_mods_def,expr_post_def]) >>
     strip_tac >>
     qpat_assum `is_word_type (expr_type e)`
       (fn th => qpat_assum `expr_val_rel _ _ _ _ _`
         (mp_tac o REWRITE_RULE [MATCH_MP post_value_type_word th])) >>
     simp[expr_val_rel_def]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by fs[ptr_val_ok_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all scalar_convert_origin_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  Cases_on `convert_result cx (expr_type e) dst v`
  >- suspend "success" >>
  suspend "failure"
QED

Resume convert_scalar_suffix[success]:
  qpat_x_assum `!w. INL _ = INL w ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  rename1 `state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx)` >>
  rename1 `op_prov Gu out = NONE` >> rename1 `op_taint tnu out = {}` >>
  qexistsl_tac [`Gu`,`mid`,`INL x'`,`u`,`tnu`] >> BETA_TAC >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `alloca_inv t` by fs[expr_post_mods_def,expr_post_def,stmt_state_rel_def] >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK u,_,_)`
       (irule_at Any o Q.SPEC `DF H`) >> simp[]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  simp[expr_store_bound_word] >>
  drule_all convert_scalar_landing >> simp[]
QED

Resume convert_scalar_suffix[failure]:
  `writes_fresh sm (emitted_insts sm sb)` by
    (drule_all bodyPtrTypeBuiltinsScalarRawOutcomeTheory.scalar_dispatch_straight_fresh >>
     disch_then (qspecl_then [`x`,`cenv`] (mp_tac o REWRITE_RULE [straight_fresh_def])) >>
     disch_then (drule_then strip_assume_tac) >> simp[]) >>
  `EVERY (\i. fresh_write_op i.inst_opcode) (emitted_insts sm sb)` by
    fs[writes_fresh_def, listTheory.EVERY_MEM] >>
  drule_then assume_tac scalar_convert_emitted_no_unreachable >>
  `!a u. run_inst_seq (emitted_insts sm sb) t = Abort a u ==> a = Revert_abort` by
    (rpt strip_tac >> drule_all fresh_run_abort_revert >> simp[]) >>
  drule_all scalar_convert_revert_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  rename1 `gas_origin_ptr_path _ _ _ (Abort Revert_abort u,Gu,tnu)` >>
  qexistsl_tac [`Gu`,`mid`,`Abort Revert_abort u`,`INR (Error (RuntimeError msg))`,`tnu`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_not_halt]
QED
Finalise convert_scalar_suffix

val scalar_child_post = ``\(H : (bool # 256 word # type_value) list # num list)
  (res:value + exception) mid G tn t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x t /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ptr_val_ok cx (expr_type e) v x G tn t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next``;

Theorem convert_scalar_reached_type[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL v,mid) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  value_has_type tv v
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac runtime_consistent_get_tenv >>
  gvs[value_runtime_typed_def]
QED

Theorem convert_scalar_compose[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  valid_conversion (expr_type e) dst /\ ~is_bytestring_type (expr_type e) /\
  is_word_type (expr_type e) /\ is_word_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    ^scalar_child_post ^scalar_convert_exit ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx (TypeBuiltin dst Convert dst [e])) (read_result cx))
    (es,s0,G0,tn0) ^scalar_convert_post ^scalar_convert_exit
Proof
  strip_tac >> PURE_REWRITE_TAC[convert_scalar_source] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL v) mid (OK t)` >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >~ [`storage_trace_frame (\ee. (convert_result _ _ _ _,ee))`]
  >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res ee G tn t. (^scalar_child_post) H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> BETA_TAC >> conj_tac
  >- suspend "reached" >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> BETA_TAC >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]
QED

Resume convert_scalar_compose[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all_then assume_tac convert_scalar_reached_type >>
  irule convert_scalar_suffix >> simp[] >> qexistsl_tac [`sm`,`x`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >> gvs[]
QED
Finalise convert_scalar_compose

Theorem convert_scalar_stack[local]:
  ~is_bytestring_type (expr_type e) ==>
  !sa. ?out sb. compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa =
              (StackValue dst out,sb)
Proof
  rpt strip_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  Cases_on `compile_type_convert x (case dst of FlagT name =>
       ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
       | _ => mk_convert_op (expr_type e) dst) sm` >>
  drule_all_then (irule_at Any) convert_scalar_compile_cut
QED

Theorem convert_scalar_lower_cuts[local]:
  ~is_bytestring_type (expr_type e) /\ gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa = (out,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) sha = (out,shb) ==>
  compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa = (StackValue dst out,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) sha = (StackValue dst out,shb)
Proof
  strip_tac >>
  `?a b. compile_expr cenv ty (TypeBuiltin dst Convert dst [e]) sa =
     (StackValue dst a,b)` by (irule convert_scalar_stack >> simp[]) >>
  `gas_shadow_compiles (compile_expr cenv ty (TypeBuiltin dst Convert dst [e]))
     (compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (TypeBuiltin dst Convert dst [e])))` by
    irule gas_shadow_stmt_compile_expr_env >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (TypeBuiltin dst Convert dst [e])) sha` >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem convert_scalar_run[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  valid_conversion (expr_type e) dst /\ ~is_bytestring_type (expr_type e) /\
  is_word_type (expr_type e) /\ is_word_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin dst Convert dst [e]) es
Proof
  strip_tac >> simp[expr_sim_full_mods_def, post_value_type_def, expr_type_def] >>
  rpt gen_tac >> strip_tac >> simp[] >>
  rename1 `gas_shadow_state sa sha` >>
  rename1 `fn_has_code sha shb shadow_func` >>
  rename1 `lower_value _ _ _ (TypeBuiltin _ _ _ _) sa = (out,sb)` >>
  drule_all_then strip_assume_tac convert_scalar_lower_cuts >>
  drule_all_then strip_assume_tac convert_scalar_cuts >> gvs[] >>
  `local_ptrs_reserved cenv sm /\ (!z. not_fresh_at sa z ==> not_fresh_at sm z)` by
    (conj_tac >- (drule_all local_ptrs_reserved_next_var >> simp[]) >>
     rpt strip_tac >> drule_all freshWritesTheory.not_fresh_at_mono >> simp[]) >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    metis_tac[] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule convert_operand_admissible >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (qpat_assum `lower_value _ cenv _ e sa = (x,sm)` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[compile_lower_value_var]) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e _`
    (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`x`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  irule convert_scalar_compose >> simp[] >> conj_tac
  >- (qexistsl_tac [`env`,`mods`] >> simp[]) >>
  qexistsl_tac [`sm`,`x`] >> simp[] >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> BETA_TAC >> simp[] >> rpt strip_tac >> gvs[] >>
  drule post_value_type_word >> simp[]
QED

Theorem convert_scalar_route_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok_mods mods exps cx e /\
  ~is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es /\
  (!sa. ?out sb. compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) sa =
                (StackValue dst out,sb)) /\
  (!s raw mid. eval_expr cx (TypeBuiltin ann Convert dst [e]) s = (INL raw,mid) ==>
     ?v. raw = Value v)
Proof
  strip_tac >> drule_all_then strip_assume_tac convert_scalar_pre >> gvs[] >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty st.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (irule o cj 1 o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  conj_asm1_tac
  >- (irule convert_scalar_run >> fs[optionTheory.IS_SOME_EXISTS] >>
      qexistsl_tac [`env`,`mods`] >> simp[]) >>
  `!sa. ?out sb. compile_expr cenv ty (TypeBuiltin ann Convert ann [e]) sa =
                (StackValue ann out,sb)` by (irule convert_scalar_stack >> simp[]) >>
  `!s raw mid. eval_expr cx (TypeBuiltin ann Convert ann [e]) s = (INL raw,mid) ==>
     ?v. raw = Value v` by (rpt strip_tac >> drule eval_expr_type_builtin_value >> simp[]) >>
  simp[] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule scalar_stack_vv_sim_full_mods >> simp[post_value_type_def, expr_type_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `sa` >> qpat_assum `!sa. ?out sb. compile_expr _ _ _ sa = _`
    (qspec_then `sa` strip_assume_tac) >>
  qexistsl_tac [`ann`,`out`,`sb`] >> simp[]
QED
