(* Adapt linked scalar and word-default keyword outcomes to the common head post. *)
Theory bodyExtKeywordScalarJoinMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyExtKeywordHeadRunMods
  bodyExtKeywordScalarMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  exprLowering exprLoweringProps compileEnv gasShadow gasContext
  exprSimHypsDefs exprSimSource bodyPtrDefs loweringPosts allocaHistory
  vyperInterpreter vyperState vyperTypeSystem vyperAST vyperContext
  bodyCallSupport list pair option finite_map arithmetic
  exprOperandVar exprSimWordArgs bodyMemoryDefs gasOriginPtrLabels
  bodyInvCodeProps stmtSimDefs exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeInvariants vyperExprNoControl
  exprSimDefs vyperTypeExprSoundness
Libs monadsyntax

val common = ``\(H : (bool # bytes32 # type_value) list # num list) ee G tn t.
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  t.vs_labels = s0.vs_labels /\
  (!x. op = Var x ==> not_fresh_at sb x)``;

val scalar = ``\v G tn t.
  (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
    dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
  (k = EKDefault ==> dt = rt /\ expr_val_rel cx rt v op t /\
    ptr_val_ok cx rt v op G tn t)``;

val scalar_post = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^common H ee G tn t /\ ^scalar v G tn t``;
val exit_post = ``\(H : (bool # bytes32 # type_value) list # num list)
  (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
fun outcome_for modules = ``gas_outcome_full_mods
    (DF : (bool # bytes32 # type_value) list # num list -> dead,
     lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ^modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)``;
val outcome = outcome_for ``mods : (num option # toplevel list) list``;
val raw_outcome = outcome_for ``cenv.ce_modules``;
val raw_body = ``\H v ee G tn t.
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods ((DF : (bool # bytes32 # type_value) list # num list -> dead) H)
    lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val raw_post = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^raw_body H v ee G tn t /\
  (?w. eval_operand op t = SOME w /\ dest_NumV v = SOME (w2n w) /\
    op_taint tn op = {})``;
val joined = ``\H (res : value + exception) ee G tn t. ?v. res = INL v /\
  ^raw_body H v ee G tn t /\ ^scalar v G tn t``;

Theorem keyword_common_lift[local]:
  return_buf_frame d cenv sa s0 /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ ^outcome ^joined ^exit_post ==>
  ^outcome ^scalar_post ^exit_post
Proof
  BETA_TAC >> strip_tac >>
  `^outcome (\H res ee G tn t. ^joined H res ee G tn t /\
      t.vs_labels = s0.vs_labels) ^exit_post` by
    (irule gas_outcome_full_mods_post_path >>
     goal_assum (drule_at Any) >> BETA_TAC >> rpt gen_tac >> strip_tac >>
     simp[] >> drule_then ACCEPT_TAC gas_origin_ptr_path_preserves_labels) >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o PURE_REWRITE_RULE [APPEND_NIL])) >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qexists_tac `v` >> simp[] >>
  irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]
QED

Theorem keyword_scalar_code[local]:
  ~(k = EKDefault /\ ~is_word_type rt) /\
  compile_ext_call_kwarg cfn cenv rt k e sa = ((op,dt),sb) ==>
  lower_value cfn cenv (ext_call_kw_type rt k) e sa = (op,sb) /\ dt = rt
Proof
  strip_tac >>
  `(if k = EKDefault then rt else BaseT (UintT 256)) = ext_call_kw_type rt k` by
    (Cases_on `k` >> simp[ext_call_kw_type_def]) >>
  qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_ext_call_kwarg_def,comp_bind_def,comp_return_def,LET_THM] >>
  pairarg_tac >> simp[]
QED

Theorem keyword_read_admissible:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ (_ with gas_obs := _)`
    (strip_assume_tac o MATCH_MP expr_body_pre_mods_runtime_typing) >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `no_type_error_result (INR y : value + vyperState$exception)` by
    (qpat_assum `bind _ _ _ = (INR _,_)`
       (mp_then Any mp_tac (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound)) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[runtime_consistent_def,gas_obs_type_invariants] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `no_control_exc y` by
    (qpat_assum `bind _ _ _ = (INR _,_)` mp_tac >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control,read_result_no_control]) >>
  Cases_on `y` >> gvs[expr_res_ok_def,no_control_exc_def,no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem ext_kw_scalar_join_mods:
  contract_inv mods exps ctx cenv cx /\ MEM func ctx.ctx_functions /\
  module_body_inv mods src tops cenv cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  body_expr_full_ok_mods mods exps cx e /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (~(k = EKDefault /\ ~is_word_type rt)) /\
  (k <> EKDefault ==> ^raw_outcome ^raw_post ^exit_post) /\
  expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k
    (gas_shadow_expr e) shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ^outcome ^scalar_post ^exit_post
Proof
  BETA_TAC >> strip_tac >>
  `lower_value compile_expr cenv (ext_call_kw_type rt k) e sa = (op,sb) /\ dt = rt` by
    (irule keyword_scalar_code >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lower_value compile_expr (gas_shadow_env T cenv) (ext_call_kw_type rt k)
       (gas_shadow_expr e) shadow_sa = (op,shadow_sb) /\ dt = rt` by
    (irule keyword_scalar_code >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspec_then `sa` mp_tac
       (Q.SPECL [`cenv`,`ext_call_kw_type rt k`,`e`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (qpat_assum `lower_value compile_expr cenv _ _ sa = _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] compile_lower_value_var)) >> simp[]) >>
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) keyword_common_lift) >> simp[] >>
  Cases_on `k = EKDefault`
  >- suspend "word_default"
  >> drule_then assume_tac contract_inv_cenv_modules >>
  qpat_x_assum `k <> EKDefault ==> _` mp_tac >> simp[] >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume ext_kw_scalar_join_mods[word_default]:
  gvs[ext_call_kw_type_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule_then ACCEPT_TAC keyword_read_admissible) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_mods_def] >> strip_tac >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                   _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
                    `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  simp[] >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  qhdtm_assum `expr_post_mods` (mp_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  simp[]
QED

Finalise ext_kw_scalar_join_mods
