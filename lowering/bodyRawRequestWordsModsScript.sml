(* Linked word-list prefix: the tail is reached only after the head read. *)
Theory bodyRawRequestWordsMods
Ancestors
  bodyReachedWordBindMods bodyECRecoverOperandConsPostMods bodyECArithReadAdvanceMods
  bodyFullPredsMods bodyMemoryDefs
  exprSimPrecompiles exprSimSource wordArgsPtr exprSimWordArgs vyperState
  loweringPosts exprLoweringProps exprBodyPreProps exprSimFullBundleProps
  gasShadowCompileStmtHelpers fragExec vyperTypeEvalCaseProofs exprWordOperand
  gasOutcomeFull vyperStorageTrace stmtSimForRounds freshWrites gasShadowState
  gasContext vyperTypeSystem bodyFullWordArgs bodyFullIfExpReach
  bodyFullPostsMods vyperTypeExprSoundness vyperStorageFootprint list
Libs monadsyntax

val request_entry = ``\(H : (bool # 256 word # type_value) list # num list). stmt_state_rel H ctx func cenv cx es s0 /\
  immutable_frame_mods func cenv cx es s0 /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0``;

val request_endpoint = ``\(H : (bool # 256 word # type_value) list # num list).
  typed_args_post H ctx func cenv cx es sa s0 ee ws xs vs t /\
  immutable_frame_mods func cenv cx ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Triviality eval_exprs_nil_bind:
  bind (eval_exprs cx []) k = k []
Proof
  simp[FUN_EQ_THM,bind_def,eval_exprs_nil]
QED

Triviality eval_exprs_cons_bind_request:
  bind (eval_exprs cx (e::ws)) k =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx ws) (\vs. k (v::vs)))
Proof
  once_rewrite_tac[eval_exprs_cons_action] >>
  CONV_TAC (LAND_CONV (REWR_CONV bind_assoc)) >> BETA_TAC >>
  CONV_TAC (LAND_CONV (RAND_CONV (ABS_CONV (REWR_CONV bind_assoc)))) >>
  simp[bind_return]
QED

Triviality request_word_cons_code:
  lower_word_args cenv arg_ty (e::ws) sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) arg_ty
    (MAP gas_shadow_expr (e::ws)) shadow_sa = (xs,shadow_sb) /\
  arg_ty (gas_shadow_expr e) = arg_ty e /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
  ?x ys s1 shadow_s1. xs = x::ys /\
    lower_value compile_expr cenv (arg_ty e) e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (arg_ty e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
    lower_word_args cenv arg_ty ws s1 = (ys,sb) /\
    lower_word_args (gas_shadow_env T cenv) arg_ty
      (MAP gas_shadow_expr ws) shadow_s1 = (ys,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,sb,shadow_s1,shadow_sb) /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    (!l. x <> Label l) /\ (!z. x = Var z ==> not_fresh_at s1 z)
Proof
  strip_tac >> fs[lower_word_args_cons, expr_sim_full_code_def] >> gvs[] >>
  `gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `arg_ty e`] gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule_all_then strip_assume_tac lower_value_word_shape >>
  qpat_assum `lower_value compile_expr (gas_shadow_env T _) _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_word_args cenv _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  qpat_assum `lower_word_args (gas_shadow_env T _) _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  simp[] >> rpt conj_tac >> metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl]
QED

Theorem request_word_prefix_mods:
  !ws es sa shadow_sa xs sb shadow_sb s0 G0 tn0
      (next : value list -> evaluation_state -> value evaluation_result).
  body_exprs_full_ok_mods mods exps cx ws /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  (!e mid. MEM e ws /\ expr_sim_inv_mods mods cenv cx env mid /\
     body_const_cells_agree_mods mods cx env mid ==>
     expr_body_pre_mods mods cenv cx env e mid) /\
  EVERY (is_word_type o expr_type) ws /\
  (!e. MEM e ws ==> arg_ty (gas_shadow_expr e) = arg_ty e) /\
  lower_word_args cenv arg_ty ws sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) arg_ty
    (MAP gas_shadow_expr ws) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_exprs cx ws) next) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> (^request_entry) H) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
     (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r) /\
  (!reads vs ee G tn t.
     (!tail. eval_exprs cx ws (es with gas_obs := reads ++ tail) =
         (INL vs,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> (^request_endpoint) H) /\
     LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                           value_has_type tv v) ws vs /\
     EVERY (\op. op_prov G op = NONE /\ op_taint tn op = {}) xs /\
     EVERY (\op. (!l. op <> Label l) /\ (!z. op = Var z ==> not_fresh_at sb z)) xs /\
     expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
     t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
     gas_admissible (next vs) expr_res_ok ee ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (next vs) (ee,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_exprs cx ws) next) (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> Induct
  >- (rpt gen_tac >> strip_tac >> gvs[lower_word_args_nil,eval_exprs_nil,eval_exprs_nil_bind] >>
      first_x_assum irule >>
      simp[typed_args_post_def,wb_frame_refl,ghost_kept_at_refl] >>
      rpt conj_tac >> rpt (first_assum ACCEPT_TAC ORELSE gen_tac ORELSE disch_tac)
      >- (qexists_tac `[]` >> simp[]) >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  suspend "cons"
QED

Resume request_word_prefix_mods[cons]:
  rpt gen_tac >> strip_tac >> fs[EVERY_DEF,MEM] >>
  `expr_body_pre_mods mods cenv cx env h es` by (first_assum irule >> simp[]) >>
  `arg_ty (gas_shadow_expr h) = arg_ty h` by (first_assum irule >> simp[]) >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) [] request_word_cons_code) >> gvs[] >>
  `body_expr_full_ok_mods mods exps cx h` by
    (qpat_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
     pure_once_rewrite_tac[body_exprs_full_ok_mods_def] >> strip_tac >> simp[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (arg_ty h) h es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ h`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (arg_ty h) h es /\
      expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (arg_ty h) h es` by
       (first_assum irule >> simp[] >> conj_tac
        >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
     simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> fs[expr_sim_full_code_def]) >>
  qpat_x_assum `gas_admissible (bind (eval_exprs cx (_::_)) next) _ es`
    (assume_tac o PURE_REWRITE_RULE [eval_exprs_cons_bind_request]) >>
  PURE_REWRITE_TAC [eval_exprs_cons_bind_request] >>
  irule reached_word_bind_mods >> simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`d`,`x`,`sa`,`s1`,`shadow_func`,`shadow_sa`,`shadow_s1`,`arg_ty h`] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  mp_tac (Q.INST [`gs` |-> `gas_explicit marks s0.vs_gas_readings`,
                  `e` |-> `h`, `rest` |-> `ws`, `ce` |-> `cenv`] ec_arith_read_advance_mods) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type h) = SOME tv /\ value_has_type tv v` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ mid` (drule_then assume_tac o K expr_sim_inv_mods_env) >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >> fs[value_runtime_typed_def]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
     fs[expr_post_mods_def,expr_post_def]) >>
  `ci_mono s1 sb` by
    (qpat_assum `lower_word_args cenv _ ws s1 = _`
       (ACCEPT_TAC o MATCH_MP ci_mono_lower_word_args)) >>
  qpat_x_assum `!es' sa' shadow_sa' xs' sb' shadow_sb' s0' G0' tn0' next'. _`
    (qspecl_then [`mid`,`s1`,`shadow_s1`,`ys`,`sb`,`shadow_sb`,`t`,`G1`,`tn1`,
                   `\vs. next (v::vs)`] mp_tac) >>
  BETA_TAC >>
  (impl_tac >- suspend "tail_pre") >>
  disch_then ACCEPT_TAC
QED

Resume request_word_prefix_mods[tail_pre]:
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> first_assum irule >> simp[])
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> first_assum irule >> simp[])
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  suspend "tail_cont"
QED

Resume request_word_prefix_mods[tail_cont]:
  qx_genl_tac [`reads`,`vs`,`ee`,`G`,`tn`,`u`] >> strip_tac >>
  `?obs. ee.storage_trace = mid.storage_trace ++ obs` by
    (qpat_assum `!tail. eval_exprs cx ws _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     simp[evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     typed_args_post H ctx func cenv cx es sa s0 ee (h::ws) (x::ys) (v::vs) u /\
     immutable_frame_mods func cenv cx ee u /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
     op_prov G x = NONE /\ op_taint tn x = {} /\
     (!z. x = Var z ==> not_fresh_at sb z)` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (irule valid_horizon_append >> metis_tac[]) >>
     `valid_horizon cx st0 H es.storage_trace` by
       (irule valid_horizon_append >> metis_tac[]) >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos hd) (mp_tac o SPEC_ALL)
         (Q.INST [`rest` |-> `ws`, `sm` |-> `sb`] ecrecover_operand_cons_post_mods)) >>
     BETA_TAC >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                   (qexists_tac `tv` >> simp[]))) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (pure_rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> typed_args_post H _ _ _ _ es _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!reads vs ee G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (next vs) _ _ _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings ++ reads`,`v::vs`,`ee`,`G`,`tn`,`u`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qx_gen_tac `tail` >> pure_once_rewrite_tac[eval_exprs_cons_action] >>
    pure_once_rewrite_tac[bind_def] >> pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
    qpat_assum `!tail. bind (eval_expr cx h) _ _ = _`
      (qspec_then `reads ++ tail` (fn th => simp[th])) >>
    pure_once_rewrite_tac[bind_def] >> simp[return_def])) >>
  disch_then ACCEPT_TAC
QED

Finalise request_word_prefix_mods
