(* Linked word-list operands of literal membership. *)
Theory bodyMembershipLiteralOperandsMods
Ancestors
  bodyArrayOperandMods bodyFullPredsMods bodyFullPostsMods bodyWriteSubscriptSourceMods
  exprBodyPreProps exprSimBopInLiteralWord exprSimSliceCompose exprSimWordArgs wordArgsPtr
  exprWordOperand exprSimFullBundleProps bodyFullWordArgs bodyInvCodeProps
  gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods gasStorage exprLoweringProps loweringPosts vyperStorageTrace
  vyperStorageFootprint bodyPtrDefs fragGasOriginPtr vyperState
  vyperTypeSystem vyperTypeBuiltins vyperTypeCallGraph vyperTypeCallStackSoundness
  supportedExprTraverse allocLimits exprSimHypsDefs bodyMemoryDefs freshWrites vyperAST
  vyperInterpreter vyperContext list immutableRegionTypingProps immutableRegionFrameProps
  bodyInvSplit bodyFullShadowBodyInv exprSimDefs gasContext bodyFullIfExpReach fragExec
Libs monadsyntax

Theorem literal_membership_typing_mods:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  ann = BaseT BoolT /\ a = ArrayT (expr_type e1) n /\ t = SOME (expr_type e1) /\
  compatible_bound n (LENGTH elems) /\ EVERY (\e. expr_type e = expr_type e1) elems
Proof
  strip_tac >> drule_then mp_tac expr_body_pre_mods_well_typed >>
  simp[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def] >>
  metis_tac[literal_membership_typing]
QED

Theorem literal_membership_judgments_mods:
  body_expr_full_ok_mods mods exps cx e1 /\
  ((?s raw s' s1 v s1'. eval_expr cx e1 s = (INL raw,s') /\
      read_result cx raw s1 = (INL v,s1')) ==>
    body_expr_full_ok_mods mods exps cx (Builtin a (MakeArray t n) elems)) /\
  compatible_bound n (LENGTH elems) ==>
  body_exprs_full_ok_mods mods exps cx (e1::elems)
Proof
  strip_tac >> pure_once_rewrite_tac[body_expr_full_ok_mods_def] >>
  simp[] >> strip_tac >> irule make_array_operand_elements_mods >>
  qexistsl_tac [`a`,`n`,`t`] >> simp[builtin_args_length_ok_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

Triviality membership_gas_obs_frame:
  immutable_frame_mods func cenv cx (es with gas_obs := gs) s =
    immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx (es with gas_obs := gs) locs =
    storage_well_formed_on cx es locs
Proof
  conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def,
          immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
          loweringStateRelDefsTheory.immutables_rel_def] >>
  irule storage_well_formed_on_backends >> simp[]
QED

val list_post = ``
  ?vs. (res : value list + exception) = INL vs /\
    stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ee u /\
    immutable_frame_mods func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\
    EVERY (value_has_type tv) vs /\
    LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) xs vs /\
    EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs /\
    wb_frame cenv es ee sa s0 u /\
    (~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 u) /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val list_exit = ``expr_exit (res : value list + exception) r /\
  halt_exit (H : (bool # 256 word # type_value) list # num list) cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Triviality membership_list_nil:
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx []) (es,s0,G0,tn0)
    (\H res ee G tn u. (\args xs sb. ^list_post) [] [] sa) (\H res ee gt r. ^list_exit)
Proof
  BETA_TAC >> strip_tac >> gvs[] >> irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL []`,`s0`,`tn0`] >>
  simp[eval_exprs_nil, return_def, gas_origin_ptr_path_rules, wb_frame_refl,
       ghost_kept_at_refl, membership_gas_obs_frame] >>
  rpt strip_tac >> qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Triviality membership_gas_cons_map:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind source (\vs. return ((v:value)::vs))) (es,s,G,tn)
    (\H raw ee G' tn' t. ?res. raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
      Q H res ee G' tn' t)
    (\H raw ee gt r. ?res. raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
      R H res ee gt r)
Proof
  strip_tac >>
  `ignore_bind (bind source (\vs. return (v::vs))) (return ()) =
   ignore_bind source (return ())` by simp[ignore_bind_def, bind_assoc, bind_return] >>
  `!x. SND (bind source (\vs. return (v::vs)) x) = SND (source x)` by
    (gen_tac >> Cases_on `source x` >> rename1 `source x = (res0,st1)` >>
     Cases_on `res0` >> simp[bind_def, return_def]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  simp[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR ex => INR ex`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (gen_tac >> simp[bind_def, return_def] >> Cases_on `res` >> simp[]) >>
      simp[] >> gen_tac >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac)
      >- (simp[] >> disj1_tac >> qexists_tac `res` >> simp[])
      >> simp[] >> disj2_tac >> conj_tac
      >- (qspec_then `\raw. case raw of INL vs => INL (v::vs) | INR ex => INR ex`
            mp_tac (Q.GEN `f` createSizeExitTheory.create_size_exit_ok_map) >>
          simp[])
      >> qexists_tac `res` >> simp[])
  >> disj2_tac >> disj2_tac >> metis_tac[]
QED

Triviality membership_arg_calls:
  !args e k. MEM e args /\ MEM k (int_calls_expr e) ==> MEM k (int_calls_exprs args)
Proof
  Induct >> simp[int_calls_expr_def] >> metis_tac[]
QED

Triviality membership_builtin_arg_pre:
  expr_body_pre_mods mods cenv cx env (Builtin a b args) es /\ MEM e args /\
  (!n. b <> Slice n) /\ expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, EXISTS_MEM, EVERY_MEM] >>
  strip_tac >>
  `!p. supported_expr_exists p e ==> supported_expr_exists p (Builtin a b args)` by
    (simp[Once supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  drule_all_then assume_tac constSubstCorrectTheory.frame_well_typed_exprs_member >>
  drule_all_then assume_tac exprSimSourceTheory.byte_widths_exprs_mem >>
  `alloc_limits_expr cenv e` by
    (irule exprSimSourceTheory.alloc_limits_builtin_arg >>
     qexistsl_tac [`a`,`args`,`b`] >> simp[]) >>
  simp[] >> rpt conj_tac
  >- (irule call_evaluation_safe_mono >> qexists_tac `int_calls_exprs args` >>
      simp[] >> metis_tac[membership_arg_calls])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[membership_arg_calls]
  >> metis_tac[]
QED

Triviality membership_operand_pre:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) base_es /\
  MEM e (e1::elems) /\ expr_sim_inv_mods mods cenv cx env es ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >> gvs[]
  >- (irule membership_builtin_arg_pre >>
      qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (Bop _) _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env (Builtin a (MakeArray t n) elems) es` by
    (irule membership_builtin_arg_pre >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (Bop _) _) _` (irule_at Any) >> simp[]) >>
  irule membership_builtin_arg_pre >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (MakeArray _ _) _) _` (irule_at Any) >> simp[]
QED

Triviality membership_value_sim:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Triviality membership_value_shape:
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,s1) ==>
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule_all lower_value_word_shape >> simp[]
QED

Triviality membership_word_arg_code:
  lower_word_args cenv expr_type (e::args) sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) expr_type
      (MAP gas_shadow_expr (e::args)) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
  ?x s1 shadow_s1 ys. xs = x::ys /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
    lower_word_args cenv expr_type args s1 = (ys,sb) /\
    lower_word_args (gas_shadow_env T cenv) expr_type
      (MAP gas_shadow_expr args) shadow_s1 = (ys,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,sb,shadow_s1,shadow_sb) /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id
Proof
  simp[lower_word_args_cons, expr_sim_full_code_def] >> strip_tac >>
  gvs[] >>
  `gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e`] gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_assum `lower_value compile_expr cenv _ _ _ = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value compile_expr (gas_shadow_env T _) _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_word_args cenv _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  qpat_assum `lower_word_args (gas_shadow_env T _) _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  simp[] >> rpt conj_tac >> metis_tac[fragExecTheory.fn_has_code_mid, compileEnvTheory.cs_extends_refl]
QED

val list_ok = ``\rr : value list + exception. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)``;

Triviality membership_list_head_admissible:
  gas_admissible (eval_exprs cx (e::args)) ^list_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def, eval_exprs_cons_action] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Triviality membership_list_forced_cuts:
  body_exprs_full_ok_mods mods exps cx (e::args) /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  gas_admissible (eval_exprs cx (e::args)) ^list_ok es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := marks ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
  mid.gas_obs = [] /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  body_exprs_full_ok_mods mods exps cx args /\
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  value_has_type tv v /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  gas_admissible (eval_exprs cx args) ^list_ok mid
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := marks) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th])) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := marks) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := marks)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then (assume_tac o SRULE []) (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >>
  drule_then strip_assume_tac (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
      first_x_assum irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_admissible (eval_exprs _ (_::_)) _ _` mp_tac >>
  rewrite_tac[gas_admissible_def, eval_exprs_cons_action] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >- simp[] >>
  first_x_assum (qspec_then `marks ++ gs` mp_tac) >>
  simp[bind_def] >> disch_then irule >> goal_assum (drule_at Any)
QED

Triviality membership_clean_op:
  ghost_kept_at lo cenv mid s1 G1 tn1 t G tn /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  op_prov G1 x = NONE /\ op_taint tn1 x = {} ==>
  op_prov G x = NONE /\ op_taint tn x = {}
Proof
  Cases_on `x` >> simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >>
  rewrite_tac[ghost_kept_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[ptrDisciplineTheory.op_taint_def]
QED

val post_at = ``\xs es sa s0 G0 tn0 H res ee G tn u. ^list_post``;

Triviality membership_cons_end:
  ^post_at ys mid s1 t G1 tn1 H (INL vs) ee G tn u /\
  expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  op_prov G1 x = NONE /\ op_taint tn1 x = {} /\ value_has_type tv v ==>
  (\args. ^post_at (x::ys) es sa s0 G0 tn0 H (INL (v::vs)) ee G tn u) (e::args)
Proof
  BETA_TAC >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac literal_word_post_cons >>
  drule_all_then strip_assume_tac membership_clean_op >>
  qpat_x_assum `LIST_REL _ (_::_) (_::_)` (strip_assume_tac o SRULE []) >>
  simp[] >> conj_tac
  >- (strip_tac >> irule exprSimPropsTheory.pure_frame_trans >>
      qhdtm_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
      qpat_assum `wb_frame cenv mid ee s1 t u`
        (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
      simp[] >> qexistsl_tac [`mid`,`s1`,`t`] >> simp[]) >>
  irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
  simp[] >> conj_tac >- (qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`G1`,`mid`,`mid`,`t`,`s1`,`tn1`] >>
  drule_then assume_tac expr_post_frame >> simp[]
QED

val list_input = ``
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods cenv cx env es /\
  (!e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env e st) /\
  (!e. MEM e args ==> is_word_type (expr_type e) /\
        evaluate_type (get_tenv cx) (expr_type e) = SOME tv) /\
  body_exprs_full_ok_mods mods exps cx args /\
  gas_admissible (eval_exprs cx args) ^list_ok es /\
  lower_word_args cenv expr_type args sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

Triviality membership_list_run:
  !args DF lo d PG mods exps src tops ctx shadow_ctx func shadow_func cenv cx env
     tv st0 es sa xs sb shadow_sa shadow_sb s0 G0 tn0.
  ^list_input ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (\H res ee G tn u. ^list_post) (\H res ee gt r. ^list_exit)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[lower_word_args_nil] >>
      match_mp_tac (SRULE [] membership_list_nil) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac membership_word_arg_code >> gvs[] >>
  `expr_body_pre_mods mods cenv cx env h es` by simp[] >>
  `is_word_type (expr_type h) /\ evaluate_type (get_tenv cx) (expr_type h) = SOME tv` by simp[] >>
  drule_all_then strip_assume_tac membership_value_shape >>
  drule_then assume_tac membership_list_head_admissible >>
  `body_expr_full_ok_mods mods exps cx h` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type h) h es` by
    (irule membership_value_sim >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  fs[expr_sim_full_code_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_outcome_full_mods_bind_all >>
  BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame (bind (eval_exprs _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return] >>
  qexists_tac `\H res mid G1 tn1 t. childQ H res mid G1 tn1 t /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)` >>
  reverse conj_tac >- suspend "head" >> suspend "tail"
QED

Resume membership_list_run[head]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res mid G1 tn1 t. childQ H res mid G1 tn1 t /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`,`childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> gen_tac >> Cases >> simp[halt_exit_def] >>
      rpt strip_tac >>
      qpat_assum `expr_exit (INR _ : value + exception) _` mp_tac >>
      pure_once_rewrite_tac[INST_TYPE [alpha |-> ``:value``, beta |-> ``:value list``]
        stmtSimPropsTheory.expr_exit_INR_type] >> simp[]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume membership_list_run[tail]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `?v. res = INL v /\ _` strip_assume_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac membership_list_forced_cuts >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ParentQ ParentR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules
     cx st0 (eval_exprs cx args) (mid,t,G1,tn1)
     (\H res ee G tn u. ^post_at ys mid s1 t G1 tn1 H res ee G tn u)
     (\H res ee gt r. ^list_exit)` by suspend "ih" >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any membership_gas_cons_map >>
  qexistsl_tac [`\H res ee gt r. ^list_exit`,
                `\H res ee G tn u. ^post_at ys mid s1 t G1 tn1 H res ee G tn u`] >>
  BETA_TAC >> conj_tac >- first_assum (ACCEPT_TAC o BETA_RULE) >>
  reverse conj_tac
  >- (simp[Abbr `ParentR`] >> rpt gen_tac >> strip_tac >> Cases_on `res'` >>
      gvs[halt_exit_def]) >>
  suspend "cons"
QED

Resume membership_list_run[ih]:
  qunabbrev_tac `ParentR` >> BETA_TAC >> simp[] >> first_x_assum irule >> simp[] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> first_x_assum irule >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> first_x_assum irule >> simp[])
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (strip_assume_tac o SRULE [expr_post_mods_def, expr_post_def]) >> simp[])
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- (qexistsl_tac [`shadow_func`,`shadow_s1`,`shadow_sb`] >> simp[])
  >- (irule return_buf_frame_frame >>
      qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
      qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >> simp[]) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume membership_list_run[cons]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. bind (eval_exprs _ _) _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame)) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame)) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SRULE []) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qunabbrev_tac `ParentQ` >> SIMP_TAC (srw_ss()) [] >>
  match_mp_tac (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [])) membership_cons_end) >>
  qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ mid _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ mid _ _ _` (irule_at Any) >>
  fs[ptr_val_ok_def, post_value_type_word]
QED

Finalise membership_list_run

Theorem literal_membership_action_flat_mods:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv ==>
  bind (eval_expr cx (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]))
       (read_result cx) =
  bind (eval_exprs cx (e1::elems))
    (\vs. return (BoolV (if bop = In then MEM (HD vs) (TL vs)
                        else ~MEM (HD vs) (TL vs))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac literal_membership_typing_mods >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `well_formed_type env.type_defs a` by
    (drule_then mp_tac expr_body_pre_mods_well_typed >>
     simp[well_typed_expr_def]) >>
  qpat_x_assum `a = _` SUBST_ALL_TAC >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `evaluate_type (get_tenv cx) (ArrayT (expr_type e1) n) = SOME (ArrayTV tv n)` by
    (qpat_x_assum `well_formed_type _ (ArrayT _ _)` mp_tac >>
     simp[well_formed_type_def, vyperValueTheory.evaluate_type_def]) >>
  drule_all_then (fn th => rewrite_tac[th]) literal_membership_action >>
  rewrite_tac[eval_exprs_cons_action, vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  simp[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return]
QED

Theorem bop_in_literal_operands_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\ evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
  body_expr_full_ok_mods mods exps cx e1 /\
  ((?s raw s' s1 v s1'. eval_expr cx e1 s = (INL raw,s') /\
      read_result cx raw s1 = (INL v,s1')) ==>
    body_expr_full_ok_mods mods exps cx (Builtin a (MakeArray t n) elems)) /\
  gas_admissible
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]))
          (read_result cx)) expr_res_ok es /\
  lower_word_args cenv expr_type (e1::elems) sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr (e1::elems))
    shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_exprs cx (e1::elems)) (es,s0,G0,tn0)
    (\H res ee G tn u. (\args. ^list_post) (e1::elems)) (\H res ee gt r. ^list_exit)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (fn th => qpat_x_assum `gas_admissible _ _ _` (assume_tac o REWRITE_RULE [th]))
    literal_membership_action_flat_mods >>
  `gas_admissible (eval_exprs cx (e1::elems)) ^list_ok es` by
    (drule_at (Pat `gas_admissible _ _ _`) slice_gas_admissible_bind_head >> simp[]) >>
  drule_all_then strip_assume_tac literal_membership_typing_mods >>
  drule_all_then assume_tac literal_membership_judgments_mods >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `!e. MEM e (e1::elems) ==> is_word_type (expr_type e) /\
       evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    (simp[] >> rpt strip_tac >> qpat_x_assum `EVERY _ elems` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  irule membership_list_run >> asm_rewrite_tac[] >>
  conj_tac >- (qexistsl_tac [`shadow_func`,`shadow_sa`,`shadow_sb`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  rpt strip_tac >> irule membership_operand_pre >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (Bop _) _) _` (irule_at Any) >> simp[]
QED
