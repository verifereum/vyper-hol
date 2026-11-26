(* Linked checked signed negation. The operand is forced before its
   read-only arithmetic suffix; a failed signed bound aborts at ASSERT. *)
Theory bodyWordNegRouteMods
Ancestors
  bodyFullBuiltinWordNeg bodyFullPredsMods bodyScalarStackVVMods
  bodyForRangeScalarFrameMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods exprBodyPreProps exprWordOperand
  gasShadowCompileStmtHelpers gasShadowState vyperStorageTrace
  vyperTypeExprSoundness exprSimWordArgs stateRelProj
  vyperAST vyperTyping vyperTypeSystem compileEnv allocLimits supportedExprTraverse
  exprSimHypsDefs vyperTypeCallGraph exprLoweringProps fragExec
  exprSimUnopProps vyperInterpreter vyperContext loweringPosts list
  bodyFullPostsMods venomState exprSimProps loweringStateRelDefs finite_map
  freshWrites rich_list bodyPtrDefs exprSimMemDefs exprLowering vyperState
  gasContext gasExemptCertMods exprSimDefs exprSimUnopComposeProps
  fragGasSeqPtr exprSimSource vyperStorageFootprint ptrDiscipline
  bodyFullShadowBodyInv exprBopSimProps

Theorem neg_operand_pre[local]:
  expr_body_pre_mods mods cenv cx env (Builtin a Neg args) es ==>
  ?e. args = [e] /\ a = expr_type e /\ is_numeric_type (expr_type e) /\
      ~is_uint_type (expr_type e) /\ is_word_type (expr_type e) /\
      expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def,
       Excl "is_numeric_type_def"] >> strip_tac >>
  Cases_on `args` >> gvs[Excl "is_numeric_type_def"] >>
  rename1 `Builtin _ Neg [e]` >>
  `is_word_type (expr_type e)` by
    (qpat_assum `is_numeric_type (expr_type e)` mp_tac >>
     simp[NoAsms, is_numeric_type_def] >> strip_tac
     >- (Cases_on `expr_type e` >> fs[is_int_type_def] >>
         rename1 `is_int_type (BaseT b)` >> Cases_on `b` >>
         fs[is_int_type_def, is_word_type_def]) >> simp[is_word_type_def]) >>
  simp[Excl "is_numeric_type_def"] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ Neg _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, constSubstCorrectTheory.frame_well_typed_exprs_cons] >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem neg_lower_cuts[local]:
  lower_value compile_expr cenv ty (Builtin (expr_type e) Neg [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin (expr_type e) Neg [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x s1 shadow_s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
    compile_neg x (expr_type e) s1 = (op,sb) /\
    gas_shadow_state s1 shadow_s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func
Proof
  strip_tac >>
  qpat_assum `lower_value _ cenv _ (Builtin _ Neg [_]) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_neg) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
        (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
          (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shadow_x = x` SUBST_ALL_TAC >>
  `compile_neg x (expr_type e) shadow_s1 = (op,shadow_sb)` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ Neg _)) _ = _` mp_tac >>
     pure_rewrite_tac[gasShadowTheory.gas_shadow_expr_def,
       gasShadowTheory.gas_shadow_builtin_def, MAP] >>
     simp[NoAsms] >> disch_then (strip_assume_tac o MATCH_MP lower_value_neg) >>
     gvs[gasShadowTheory.gas_shadow_expr_type]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\ cs_extends shadow_sa shadow_s1` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb /\ cs_extends shadow_s1 shadow_sb` by
    metis_tac[straight_fresh_cs_extends, CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg] >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`] >> simp[] >>
  metis_tac[fn_has_code_split]
QED

Theorem neg_child_typed[local]:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,mid) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := readings) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := readings)` by
    simp[body_const_cells_agree_mods_branch_updates] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     simp[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  gvs[value_runtime_typed_def] >> qexists_tac `tv` >> simp[]
QED

Theorem neg_parent_post[local]:
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  u = (t with vs_vars := vars) with vs_inst_idx := idx /\
  local_ptrs_reserved cenv s1 /\
  (!y. not_fresh_at s1 y ==> lookup_var y u = lookup_var y t) /\
  expr_val_rel cx (expr_type e) v' op u /\ is_word_type (expr_type e) /\
  sa.cs_next_var <= s1.cs_next_var ==>
  expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Neg [e])
    es sa sb s0 mid v' op u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  rewrite_tac[expr_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (`stmt_state_rel H ctx func cenv cx mid (t with vs_vars := vars)` by
       (irule stmt_state_rel_vars_frame >> drule expr_post_state >>
        strip_tac >> simp[] >> gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
     qpat_x_assum `u = _` SUBST_ALL_TAC >>
     pure_once_rewrite_tac[GSYM venom_state_fupdcanon] >>
     simp[stmt_state_rel_inst_idx]) >>
  `u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section` by
    (qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `u = _` kall_tac >> conj_tac
  >- (irule expr_post_unop >> simp[] >> qexistsl_tac [`s1`,`t`,`v`,`x`] >> simp[]) >>
  irule immutable_frame_mods_exterior_frame >>
  qexistsl_tac [`mid`,`t`,`s1`] >> simp[]
QED

Theorem neg_operand_fresh[local]:
  lower_value compile_expr cenv ty e sa = (x,s1) /\
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
  !z. x = Var z ==> not_fresh_at s1 z
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (drule logArgumentTypeEvalTheory.consistent_variable_type_well_formed >> simp[]) >>
  drule lower_value_word_shape >> disch_then drule_all >> simp[]
QED

Theorem neg_code_cut[local]:
  compile_neg x ty s1 = (op,sb) /\ fn_has_code s1 sb func /\
  t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  sb.cs_current_bb = s1.cs_current_bb /\
  sb.cs_current_insts = s1.cs_current_insts ++ emitted_insts s1 sb /\
  ?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >>
  `sb.cs_current_bb = s1.cs_current_bb /\
   sb.cs_current_insts = s1.cs_current_insts ++ emitted_insts s1 sb` by
    (qspec_then `ty` mp_tac (Q.SPEC `x` straight_fresh_neg) >>
     simp[straight_fresh_def] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `fn_has_code _ _ _` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  qexists_tac `bb` >> conj_tac >- metis_tac[] >>
  qpat_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
  pure_rewrite_tac[IS_PREFIX_APPEND] >>
  disch_then (qx_choose_then `rest` SUBST1_TAC) >>
  qexists_tac `rest` >>
  qpat_assum `sb.cs_current_insts = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_PREFIX] >> REFL_TAC
QED

Theorem neg_success_post[local]:
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  t'.vs_vars = vars /\ t' = t with vs_vars := vars /\
  (!z. not_fresh_at s1 z ==> lookup_var z t' = lookup_var z t /\
    FLOOKUP G' z = FLOOKUP G1 z /\ op_taint tn' (Var z) = op_taint tn1 (Var z)) /\
  tn'.t_mem = tn1.t_mem /\ tn'.t_stor = tn1.t_stor /\
  tn'.t_trans = tn1.t_trans /\ tn'.t_imm = tn1.t_imm /\
  local_ptrs_reserved cenv s1 /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  expr_val_rel cx (expr_type e) v' op t' /\ is_word_type (expr_type e) /\
  sa.cs_next_var <= s1.cs_next_var ==>
  expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Neg [e]) es sa sb s0
    mid v' op (t' with vs_inst_idx := idx) /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' (t' with vs_inst_idx := idx) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!z. not_fresh_at s1 z ==> lookup_var z (t' with vs_inst_idx := idx) = lookup_var z t` by
    (rpt strip_tac >> qpat_assum `!z. not_fresh_at s1 z ==> _` (drule_then strip_assume_tac) >>
     gvs[lookup_var_def]) >>
  conj_tac
  >- (irule neg_parent_post >>
      qpat_assum `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl_tac [`vars`,`idx`] >> gvs[expr_val_rel_def, eval_operand_def, lookup_var_def]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl_tac [`G1`,`mid`,`t`,`s1`,`tn1`] >> simp[lookup_var_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Theorem neg_suffix_normal[local]:
  compile_neg x (expr_type e) s1 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  eval_operand x t = SOME (typed_val_to_w256 tv v) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  w2i (FST (type_bounds (expr_type e))) < w2i (typed_val_to_w256 tv v) /\
  unop_result cx (expr_type e) Neg [expr_type e] v mid = INL v' /\
  typed_val_to_w256 tv v' = 0w - typed_val_to_w256 tv v /\
  op_taint tn1 x = {} /\ op_prov G1 x = NONE /\ allocas_from lo t /\ ~t.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions) /\
  sb.cs_current_bb = t.vs_current_bb /\
  LENGTH sb.cs_current_insts = t.vs_inst_idx + LENGTH (emitted_insts s1 sb) /\
  local_ptrs_reserved cenv s1 /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  sa.cs_next_var <= s1.cs_next_var /\ is_word_type (expr_type e) /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (\s. (unop_result cx (expr_type e) Neg [expr_type e] v s,s)) (mid,t,G1,tn1)
    (\H res ee G tn u. ?j. res = INL j /\
      expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Neg [e])
        es sa sb s0 ee j op u /\
      expr_store_bound cx (expr_type e) j op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (expr_type e) j op G tn u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all word_neg_success_origin >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`] (qx_choose_then `t'`
    (qx_choose_then `G'` (qx_choose_then `tn'` (map_every assume_tac o CONJUNCTS))))) >>
  `inst_seq_ptr (DF (storage_trace_horizon mid.storage_trace)) lo ctx func PG G1 tn1
    (emitted_insts s1 sb) t G' tn'` by simp[] >>
  drule_all_then strip_assume_tac word_neg_result_clean >>
  drule_all_then (map_every assume_tac o CONJUNCTS) word_neg_runtime_frame >>
  drule_all_then (map_every assume_tac o CONJUNCTS) word_neg_taint_exterior >>
  `!z. not_fresh_at s1 z ==> FLOOKUP G' z = FLOOKUP G1 z /\
      op_taint tn' (Var z) = op_taint tn1 (Var z)` by
    metis_tac[word_neg_ghost_register_frame] >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`,`mid`,`INL v'`,
    `t' with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts s1 sb)`,`tn'`] >>
  conj_tac >- simp[unop_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `mid with gas_obs := [] = mid` (fn th => PURE_REWRITE_TAC [th]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `expr_val_rel cx (expr_type e) v' op t'` by
    (simp[expr_val_rel_def] >> qexists_tac `tv` >> simp[]) >>
  qabbrev_tac `idx = t.vs_inst_idx + LENGTH (emitted_insts s1 sb)` >>
  `expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Neg [e]) es sa sb s0
      mid v' op (t' with vs_inst_idx := idx) /\
   ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' (t' with vs_inst_idx := idx) /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule neg_success_post >>
     qpat_assum `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G1 tn1 t` (irule_at Any) >>
     qexists_tac `t'.vs_vars` >> simp[] >> rpt strip_tac >>
     qpat_assum `!z. not_fresh_at s1 z ==> lookup_var z t' = _`
       (drule_then assume_tac) >> simp[]) >>
  `t'.vs_current_bb = t.vs_current_bb /\ t'.vs_alloca_next = t.vs_alloca_next /\
   allocas_below_fmp (t' with vs_inst_idx := idx) = allocas_below_fmp t` by
    (qpat_assum `t' = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[allocas_below_fmp_def]) >>
  qpat_x_assum `t' = _` kall_tac >>
  simp[expr_store_bound_word, ptr_val_ok_word]
QED

Theorem neg_suffix_abort[local]:
  compile_neg x (expr_type e) s1 = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  eval_operand x t = SOME w /\
  ~(w2i (FST (type_bounds (expr_type e))) < w2i w) /\
  unop_result cx (expr_type e) Neg [expr_type e] v mid = INR (Error (RuntimeError m)) /\
  op_taint tn1 x = {} /\ allocas_from lo t /\ ~t.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts s1 sb) (DROP t.vs_inst_idx bb.bb_instructions) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (\s. (unop_result cx (expr_type e) Neg [expr_type e] v s,s)) (mid,t,G1,tn1) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all word_neg_run_nonfresh >> simp[] >> strip_tac >>
  drule_all word_neg_abort_origin >>
  disch_then (qspecl_then [`explicit`,`PG`,`G1`] strip_assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rename1 `run_inst_seq _ t = Abort Revert_abort u` >>
  qexistsl_tac [`G'`,`mid`,`INR (Error (RuntimeError m))`,`tn'`,
    `u with vs_inst_idx := SUC t.vs_inst_idx`] >>
  simp[unop_result_gas_obs, exit_result_def, expr_exit_def, halt_exit_def]
QED

Theorem neg_value_sim[local]:
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es /\
  is_numeric_type (expr_type e) /\ ~is_uint_type (expr_type e) /\ is_word_type (expr_type e) /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (expr_type e) Neg [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac neg_lower_cuts >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >>
     qexistsl_tac [`expr_type e`,`Neg`] >>
     simp[builtin_args_length_ok_def, precompile_builtin_def, is_self_codesize_def]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[neg_operand_fresh] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e es` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  simp[eval_expr_unop_action, Excl "is_numeric_type_def"] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule gas_exempt_cert_mods_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> qpat_assum `gas_exempt_cert_mods _ _ _ _ _ _ _ _`
        (ACCEPT_TAC o BETA_RULE))
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`] >- simp[storage_trace_frame_def, unop_result_def] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  suspend "landing"
QED

Resume neg_value_sim[landing]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v. res = INL v /\ _`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> disj1_tac >> qexists_tac `v` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  drule_all_then strip_assume_tac neg_child_typed >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (irule expr_val_rel_typed >> qexistsl_tac [`cx`,`expr_type e`] >> simp[] >>
     qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     qhdtm_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `post_value_type cenv e = expr_type e` by simp[] >>
     qpat_assum `post_value_type cenv e = expr_type e` (fn th =>
       qhdtm_assum `expr_val_rel` (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `op_taint tn1 x = {} /\ op_prov G1 x = NONE` by
    (`post_value_type cenv e = expr_type e` by simp[] >>
     qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ptr_val_ok_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `is_word_type (post_value_type _ _) ==> _` irule >> simp[]) >>
  drule_all_then strip_assume_tac neg_code_cut >>
  suspend "dispatch"
QED

Resume neg_value_sim[dispatch]:
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule_all neg_typed_source >> disch_then (qspec_then `mid` mp_tac) >>
  Cases_on `w2i (FST (type_bounds (expr_type e))) < w2i (typed_val_to_w256 tv v)` >>
  simp[expr_type_def, post_value_type_word, Excl "is_numeric_type_def"] >> strip_tac
  >- suspend "normal"
  >> qunabbrev_tac `childR` >> irule neg_suffix_abort >>
  qpat_assum `eval_operand x t = _` (irule_at Any) >>
  qpat_assum `unop_result _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sb`,`s1`,`op`,`bb`] >> simp[]
QED

Resume neg_value_sim[normal]:
  qpat_assum `sb.cs_current_bb = s1.cs_current_bb`
    (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  `LENGTH sb.cs_current_insts = LENGTH s1.cs_current_insts + LENGTH (emitted_insts s1 sb)` by
    (qpat_assum `sb.cs_current_insts = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[NoAsms]) >>
  qpat_assum `LENGTH sb.cs_current_insts = _`
    (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  irule neg_suffix_normal >>
  qpat_assum `compile_neg _ _ s1 = _` (irule_at Any) >>
  qpat_assum `unop_result _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand x t = _` (irule_at Any) >>
  qpat_assum `lookup_block _ _ = SOME bb` (irule_at Any) >>
  simp[Excl "is_numeric_type_def"] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise neg_value_sim

Theorem word_neg_sim_mods:
  !mods exps DF lo d ctx shadow_ctx PG src tops func shadow_func cenv env cx ty a bt args es.
    bt = Neg /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `bt = Neg` SUBST_ALL_TAC >>
  drule_then strip_assume_tac neg_operand_pre >> gvs[Excl "is_numeric_type_def"] >>
  `body_expr_full_ok_mods mods exps cx e` by
    fs[builtin_args_length_ok_def, Once body_expr_full_ok_mods_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     metis_tac[]) >>
  conj_asm1_tac
  >- (irule neg_value_sim >> simp[Excl "is_numeric_type_def"] >>
      qexistsl_tac [`env`,`mods`] >> simp[]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[expr_type_def, post_value_type_word, compile_neg_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
