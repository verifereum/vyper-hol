(* Linked left-to-right operands of PowMod256. *)
Theory bodyWordPowOperandsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShared bodyFullBuiltinWordPowPost
  bodyWriteSubscriptSourceMods bodyInvCodeProps bodyFullIfExpReach
  exprBodyPreProps exprSimFullBundleProps exprSimWordBuiltins exprSimWordArgs
  exprSimAccounts exprSimSource exprLoweringProps exprWordOperand
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods gasShadowCompileStmtHelpers gasContext
  stmtSimForRounds vyperStorageTrace vyperStorageFootprint
  vyperTypeSystem vyperTypeBuiltins vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeExprSoundness constSubstCorrect supportedExprTraverse allocLimits
  bodyPtrDefs wordArgsPtr builtinMath compileEnv fragExec list
  exprSimHypsDefs exprSimDefs gasShadow vyperContext vyperInterpreter vyperState
  bodyWordModSourceCutsMods bodyWordPowSuffixMods bodyScalarStackVVMods bodyReachedWordBindMods
  loweringPosts loweringSlice exprSimMemDefs bodyMemoryDefs freshWrites
  bodyFullHashKeccakFixed finite_map words venomState ptrDiscipline vyperTypeInvariants
Libs monadsyntax

val u256 = ``BaseT (UintT 256)``;

Theorem pow_types[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann PowMod256 args) es ==>
  ?e1 e2. args = [e1;e2] /\ ann = ^u256 /\
    expr_type e1 = ^u256 /\ expr_type e2 = ^u256
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  drule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`ann`,`PowMod256`] word_builtin_modular_types)) >>
  simp[MAP_EQ_CONS] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem pow_child_pres[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann PowMod256 [e1;e2]) es ==>
  expr_body_pre_mods mods cenv cx env e1 es /\
  !mid. expr_sim_inv_mods mods cenv cx env mid ==>
        expr_body_pre_mods mods cenv cx env e2 mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  fs[frame_well_typed_exprs_cons]
QED

Theorem pow_child_sim[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_x_assum `!DF lo d PG src tops ctx sh f sf ce en ty st. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (mp_tac o REWRITE_RULE [IMP_CONJ_THM, FORALL_AND_THM]) >>
  metis_tac[]
QED

Theorem pow_source_bind[local]:
  bind (eval_expr cx (Builtin ann PowMod256 [e1;e2])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx))
    (\v. bind (bind (eval_expr cx e2) (read_result cx))
      (\w ee. (builtin_result cx ee.accounts ann PowMod256
                 [expr_type e1;expr_type e2] [v;w],ee)))
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[eval_expr_builtin_action, is_self_codesize_def, eval_exprs_cons_action,
       builtin_args_length_ok_def, precompile_builtin_def, code_slice_source_def,
       bind_assoc, bind_return]
QED

Theorem pow_shadow_cut[local]:
  gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty e sa = (x,s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (y,sh1) ==>
  y = x /\ gas_shadow_state s1 sh1
Proof
  strip_tac >> irule gas_shadow_step >>
  qpat_assum `lower_value compile_expr cenv _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
  simp[gas_shadow_stmt_lower_value_env]
QED

Theorem pow_split_code[local]:
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\ fn_has_code sa sb f ==>
  fn_has_code sa s1 f /\ fn_has_code s1 s2 f /\ fn_has_code s2 sb f
Proof
  strip_tac >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  metis_tac[fn_has_code_split]
QED

Theorem pow_paired_cuts[local]:
  lower_value compile_expr cenv ty (Builtin ann PowMod256 [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann PowMod256 [e1;e2])) sha = (op,shb) /\
  expr_sim_full_code (ctx,sh,f,sf) (sa,sb,sha,shb) ==>
  ?x y s1 s2 sh1 sh2.
    lower_value compile_expr cenv ty e1 sa = (x,s1) /\
    lower_value compile_expr cenv ty e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) sha = (x,sh1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2) sh1 = (y,sh2) /\
    compile_pow_mod256 x y s2 = (op,sb) /\ fn_has_code s2 sb f /\
    expr_sim_full_code (ctx,sh,f,sf) (sa,s1,sha,sh1) /\
    expr_sim_full_code (ctx,sh,f,sf) (s1,s2,sh1,sh2) /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    s1.cs_next_var <= s2.cs_next_var /\ s1.cs_next_id <= s2.cs_next_id
Proof
  strip_tac >> fs[expr_sim_full_code_def] >>
  drule_then strip_assume_tac lower_value_pow_mod256 >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_pow_mod256 o
      SIMP_RULE (srw_ss()) [gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  rename1 `lower_value compile_expr _ _ (gas_shadow_expr e1) sha = (sx,sh1)` >>
  rename1 `lower_value compile_expr _ _ (gas_shadow_expr e2) sh1 = (sy,sh2)` >>
  `sx = x /\ gas_shadow_state s1 sh1` by
    (irule pow_shadow_cut >>
     qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr e1) sha = _` (irule_at Any) >>
     qpat_assum `lower_value compile_expr _ _ e1 sa = _` (irule_at Any) >> simp[]) >>
  `sy = y /\ gas_shadow_state s2 sh2` by
    (irule pow_shadow_cut >>
     qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr e2) sh1 = _` (irule_at Any) >>
     qpat_assum `lower_value compile_expr _ _ e2 s1 = _` (irule_at Any) >> simp[]) >>
  gvs[] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends sha sh1 /\ cs_extends sh1 sh2` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s2 sb /\ cs_extends sh2 shb` by
    metis_tac[compile_pow_mod256_def,emit_op_extends_next_var] >>
  `fn_has_code sa s1 f /\ fn_has_code s1 s2 f /\ fn_has_code s2 sb f` by
    (irule pow_split_code >> simp[]) >>
  `fn_has_code sha sh1 sf /\ fn_has_code sh1 sh2 sf /\ fn_has_code sh2 shb sf` by
    (irule pow_split_code >> simp[]) >>
  simp[expr_sim_full_code_def] >> metis_tac[cj 2 compile_expr_grows]
QED

val pow_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem pow_forced_frame[local,simp]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

Theorem pow_gas_obs_zero[local]:
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] ==>
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)
Proof
  strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >> simp[]
QED

Theorem pow_word_operand[local]:
  expr_type e = ^u256 /\ v = IntV (&w2n (val_to_w256 v)) /\
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op s ==>
  eval_operand op s = SOME (val_to_w256 v)
Proof
  simp[expr_post_mods_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `word_value v` by
    (qpat_assum `v = IntV _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[word_value_def]) >>
  drule expr_post_word_operand >> simp[vyperValueTheory.evaluate_type_def,is_word_type_def]
QED

val pow_suffix = concl pow_mod256_suffix_mods;
val pow_stack = concl scalar_stack_vv_sim_full_mods;

Theorem pow_kept_trans[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ wb_frame cenv es mid sa s0 t ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt strip_tac >> irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >> metis_tac[]
QED

Theorem pow_kept_operand[local]:
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  eval_operand x s = SOME w /\ op_taint tn1 x = {} /\
  ghost_kept_at lo cenv mid sm (G1 : string |-> num # num) tn1 s G2 tn2 /\
  wb_frame cenv mid fin sm s t ==>
  eval_operand x t = SOME w /\ op_taint tn2 x = {}
Proof
  Cases_on `x` >> simp[eval_operand_def, op_taint_def] >>
  rw[wb_frame_def,ghost_kept_at_def] >>
  qpat_assum `!z. not_fresh_at sm z ==> _ /\ op_taint tn2 _ = _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [op_taint_def])) >> simp[]
QED

Theorem pow_state_horizon[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by simp[] >>
  drule_all_then mp_tac valid_horizon_frame >> simp[]
QED

Theorem pow_scope_dom[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  strip_tac >> drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]
QED

Theorem pow_word_shape[local]:
  lower_value compile_expr cenv ty e sa = (x,s1) /\
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = ^u256 ==>
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac lower_value_word_shape >> simp[]
QED

val pow_post = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + vyperState$exception) ee G tn t.
  ?v. res = INL v /\ expr_post_mods H ctx func cenv cx (Builtin ^u256 PowMod256 [e1;e2])
      es sa sb s0 ee v op t /\
    expr_store_bound cx ^u256 v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_val_ok cx ^u256 v op G tn t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem pow_finish[local]:
  ^pow_suffix ==>
  expr_type e1 = ^u256 /\ expr_type e2 = ^u256 /\
  v = IntV (&w2n (val_to_w256 v)) /\ w = IntV (&w2n (val_to_w256 w)) /\
  compile_pow_mod256 x y s2 = (op,sb) /\ fn_has_code s2 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  storage_trace_domain cx st0 mid.storage_trace /\ storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs1) = (INL v,mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL w,fin) /\
  fin.gas_obs = [] /\ ~u.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid v x t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ptr_val_ok cx ^u256 v x G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 mid s1 s2 t fin w y u /\
    u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    t.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
    ptr_val_ok cx ^u256 w y G2 tn2 u /\ ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (\ee. (builtin_result cx ee.accounts ^u256 PowMod256 [^u256;^u256] [v;w],ee))
    (fin,u,G2,tn2) ^pow_post ^pow_exit
Proof
  disch_then (markerLib.mk_asm "suffix") >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `eval_operand x t = SOME (val_to_w256 v)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _` (mp_then Any irule pow_word_operand) >> simp[]) >>
  `eval_operand y u = SOME (val_to_w256 w)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _` (mp_then Any irule pow_word_operand) >> simp[]) >>
  `op_taint tn1 x = {} /\ op_taint tn2 y = {}` by fs[ptr_val_ok_def,is_word_type_def] >>
  `wb_frame cenv es mid sa s0 t /\ wb_frame cenv mid fin s1 t u` by
    (conj_tac
     >- (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
         drule_then ACCEPT_TAC expr_post_frame) >>
     qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  `eval_operand x u = SOME (val_to_w256 v) /\ op_taint tn2 x = {}` by
    (irule pow_kept_operand >>
     qpat_assum `wb_frame cenv mid fin s1 t u` (irule_at Any) >>
     qexistsl_tac [`tn1`,`lo`,`G2`,`G1`] >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin u /\ immutable_frame_mods func cenv cx fin u /\
      ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
        (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  asm "suffix" (fn th => qpat_assum `compile_pow_mod256 x y s2 = _` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand x u = SOME (val_to_w256 v)` (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand y u = SOME (val_to_w256 w)` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`DF`,`lo`,`explicit`,`ctx`,`func`,`PG`,`d`,`cenv`,`cx`,`st0`,`fin`,`G2`,`tn2`,
    `^u256`,`[^u256;^u256]`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `z` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
  suspend "endpoint"
QED

Resume pow_finish[endpoint]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    (irule pow_state_horizon >> qexistsl_tac [`e1`,`mid`,`gs1`,`v`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (first_x_assum drule >> simp[]) >>
  qpat_assum `bind (eval_expr cx e1) _ _ = _` (mp_then Any assume_tac pow_scope_dom) >>
  qpat_assum `bind (eval_expr cx e2) _ _ = _` (mp_then Any assume_tac pow_scope_dom) >>
  `MAP FDOM es.scopes = MAP FDOM fin.scopes` by simp[] >>
  `wb_frame cenv es fin sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid fin s1 t u` (irule_at Any) >>
     qexistsl_tac [`func`,`cx`,`ctx`,`storage_trace_horizon mid.storage_trace`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule pow_kept_trans >>
     qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qexistsl_tac [`func`,`cx`,`ctx`,`storage_trace_horizon mid.storage_trace`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G3 tn3` by
    (irule pow_kept_trans >>
     qpat_assum `ghost_kept_at lo cenv fin s2 G2 tn2 u G3 tn3` (irule_at Any) >>
     qpat_assum `wb_frame cenv es fin sa s0 u` (irule_at Any) >>
     qexistsl_tac [`func`,`cx`,`ctx`,`storage_trace_horizon mid.storage_trace`] >> simp[]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G3`,`fin`,`INL (IntV (&w2n (word_exp (val_to_w256 v) (val_to_w256 w))))`,`z`,`tn3`] >>
  conj_tac
  >- (simp[] >> rpt (qpat_x_assum `_ = IntV _` (fn th => ONCE_REWRITE_TAC [th])) >>
      simp[valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_w2n]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[expr_post_mods_def, expr_store_bound_word, ptr_val_ok_def, is_word_type_def] >>
  suspend "parent_post"
QED

Resume pow_finish[parent_post]:
  reverse conj_tac
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx fin z`
         (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_assum `expr_post_mods H _ _ _ _ e2 _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `storage_well_formed_on cx fin (FST H)` by fs[expr_post_def] >>
  irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``, gamma |-> ``:256``]
    pow_mod256_parent_post) >>
  qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
  simp[is_word_type_def,word_value_def,valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_w2n]
QED

Finalise pow_finish

Theorem pow_value_sim[local]:
  ^pow_suffix ==>
  expr_type e1 = ^u256 /\ expr_type e2 = ^u256 /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ^u256 PowMod256 [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ^u256 PowMod256 [e1;e2]) es
Proof
  disch_then (markerLib.mk_asm "suffix") >> strip_tac >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac pow_paired_cuts >>
  drule_then strip_assume_tac pow_child_pres >>
  `body_expr_full_ok_mods mods exps cx e1` by fs[Once body_exprs_full_ok_mods_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es` by
    (irule pow_child_sim >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _` (assume_tac o PURE_REWRITE_RULE [pow_source_bind]) >>
  PURE_REWRITE_TAC [pow_source_bind] >>
  simp[post_value_type_word, vyperASTTheory.expr_type_def, is_word_type_def] >>
  irule reached_word_bind_mods >>
  qpat_assum `expr_sim_full_mods _ _ _ _ e1 es` (irule_at Any) >>
  qexistsl_tac [`sh1`,`shadow_sa`,`s1`,`sa`,`x`] >>
  fs[is_word_type_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >~ [`storage_trace_frame (bind _ _)`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_def])
  >~ [`gas_admissible _ _ _`]
  >- (qpat_assum `expr_type e1 = _` (fn t1 =>
       qpat_assum `expr_type e2 = _` (fn t2 =>
       qpat_assum `gas_admissible _ _ es` (ACCEPT_TAC o PURE_REWRITE_RULE [t1,t2]))))
  >~ [`gas_outcome_full_mods _ _ _ _ _ _ _ _`]
  >- suspend "left" >>
  rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume pow_value_sim[left]:
  qx_genl_tac [`left`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings) = (INL v,mid)` by
    (irule pow_gas_obs_zero >> simp[]) >>
  drule_all_then strip_assume_tac modular_reached_uint256_mods >>
  `expr_body_pre_mods mods cenv cx env e2 mid` by (first_x_assum drule >> simp[]) >>
  `body_expr_full_ok_mods mods exps cx e2` by fs[Once body_exprs_full_ok_mods_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (irule pow_child_sim >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[expr_post_mods_def,expr_post_def]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z /\ not_fresh_at s2 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `(!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (irule pow_word_shape >>
     qpat_assum `lower_value compile_expr _ _ e1 sa = (x,s1)` (irule_at Any) >>
     qexistsl_tac [`mods`,`es`,`env`,`cx`] >> simp[]) >>
  irule reached_word_bind_mods >>
  qpat_assum `expr_sim_full_mods _ _ _ _ e2 mid` (irule_at Any) >>
  suspend "right_entry"
QED

Resume pow_value_sim[right_entry]:
  qexistsl_tac [`sh2`,`sh1`,`s2`,`s1`,`y`] >>
  simp[is_word_type_def, storage_trace_frame_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >~ [`gas_outcome_full_mods _ _ _ _ _ _ _ _`]
  >- suspend "right" >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]
QED

Resume pow_value_sim[right]:
  qx_genl_tac [`right`,`w`,`fin`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit right t.vs_gas_readings) = (INL w,fin)` by
    (irule pow_gas_obs_zero >> simp[]) >>
  drule_all_then strip_assume_tac modular_reached_uint256_mods >>
  asm "suffix" (fn th => irule (MATCH_MP pow_finish th)) >>
  suspend "connect"
QED

Resume pow_value_sim[connect]:
  qpat_assum `compile_pow_mod256 x y s2 = _` (irule_at Any) >>
  qpat_assum `bind (eval_expr cx e1) _ _ = (INL v,mid)` (irule_at Any) >>
  qpat_assum `bind (eval_expr cx e2) _ _ = (INL w,fin)` (irule_at Any) >>
  qexistsl_tac [`tn1`,`t`,`s1`,`G1`] >> simp[] >> rpt conj_tac >> rpt strip_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED

Finalise pow_value_sim

Theorem pow_mod256_sim_from_suffix_mods:
  ^pow_suffix ==> ^pow_stack ==>
  !DF lo d ctx shadow_ctx PG mods exps src tops func shadow_func cenv env cx ty ann args es.
    (builtin_args_length_ok PowMod256 (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann PowMod256 args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin ann PowMod256 args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin ann PowMod256 args) es
Proof
  disch_then (markerLib.mk_asm "suffix") >> disch_then (markerLib.mk_asm "stack") >>
  rpt gen_tac >> strip_tac >> drule_then strip_assume_tac pow_types >> gvs[] >>
  `body_exprs_full_ok_mods mods exps cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  conj_asm1_tac
  >- (asm "suffix" (fn th => irule (MATCH_MP pow_value_sim th)) >>
      simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  asm "stack" irule >>
  simp[post_value_type_word, vyperASTTheory.expr_type_def, is_word_type_def] >>
  conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin ^u256 PowMod256 [e1;e2]) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >> strip_tac >>
      qexistsl_tac [`^u256`,`op`] >> simp[]) >>
  rpt gen_tac >> disch_then (ACCEPT_TAC o MATCH_MP eval_expr_builtin_value)
QED
