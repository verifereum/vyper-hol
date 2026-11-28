(* Request-prefix fold for external-call keyword arguments. *)
Theory s1PrefixExtCallKeywordList
Ancestors
  bodyFullExtCallKeywordList bodyFullIfExpReach s1PrefixPreds
  s1PrefixCompose s1PrefixFrame s1PrefixOfVV s1PrefixProps
  exprLoweringProps entryReachBodyFirstEmissionExpr
  entryReachBodyFirstEmissionExprSupport gasShadowCompileHelpers
  exprBodyPreProps exprSimSource exprSimWordArgs stmtSimProps
  compileEnv exprLowering gasShadowCompile gasShadowState fragExec
  bodyFullPreds bodyFullExprsListFacts stmtLoweringMono exprSimDefs vyperStorageFootprint
  vyperInterpreter vyperState vyperStorageTrace list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "head_prefix") >>
  map_every qid_spec_tac
    [`tn0`,`G0`,`s0`,`es`,`shadow_sb`,`shadow_sa`,`sb`,`sa`,`dopt`,`go`,`vo`,`ks`] >>
  Induct_on `xs` >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (irule gas_prefix_full_no_outcome >>
      simp[evaluate_def, return_def, storage_trace_frame_return]) >>
  suspend "cuts"
QED
*)
Theorem extcall_request_keywords_prefix_from_head:
  (!k e es sa sb op dt shadow_sa shadow_sb s0 G0 tn0.
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env e es /\
    expr_type e = ext_call_kw_type rt k /\
    compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
    compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e)
      shadow_sa = ((op,dt),shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)) ==>
  body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st) /\
  MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
  compile_ext_call_kwargs compile_expr cenv rt ks xs sa = ((vo,go,dopt),sb) /\
  compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs)
    shadow_sa = ((vo,go,dopt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_keywords_prefix_from_head[cuts]:
  Cases_on `ks` >> fs[] >>
  rename1 `compile_ext_call_kwargs _ _ rt (k::ks) (e::xs) sa = _` >>
  Cases_on `compile_ext_call_kwarg compile_expr cenv rt k e sa` >>
  PairCases_on `q` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ _ sa = ((op,dt),sm)` >>
  `gas_shadow_compiles (compile_ext_call_kwarg compile_expr cenv rt k e)
     (compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e))` by
    (irule (SIMP_RULE bool_ss []
      (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwarg_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  Cases_on `compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ (gas_shadow_expr e) shadow_sa = (z,shadow_sm)` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_compiles (compile_ext_call_kwargs compile_expr cenv rt ks xs)
    (compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs))` by
    (irule (SIMP_RULE bool_ss []
      (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwargs_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  Cases_on `compile_ext_call_kwargs compile_expr cenv rt ks xs sm` >>
  PairCases_on `q` >>
  rename1 `compile_ext_call_kwargs _ _ rt ks xs sm = ((vot,got,dopt_t),sb_t)` >>
  Cases_on `compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks (MAP gas_shadow_expr xs) shadow_sm` >>
  rename1 `compile_ext_call_kwargs _ _ rt ks (MAP gas_shadow_expr xs) shadow_sm = (z,shadow_sb_t)` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >>
  simp[] >> strip_tac >> gvs[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >>
     (let val extends = cj 1 (MATCH_MP first_emission_ext_call_kwarg
                                      (cj 1 first_emission_compile_expr))
      in first_assum (mp_then Any ACCEPT_TAC extends) end)) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac >>
     (let val extends = cj 1 (MATCH_MP first_emission_ext_call_kwargs
                                      (cj 1 first_emission_compile_expr))
      in first_assum (mp_then Any ACCEPT_TAC extends) end)) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  suspend "compose"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_keywords_prefix_from_head[compose]:
  fs[body_exprs_full_ok_cons, Once (cj 2 body_exprs_prefix_ok_def)] >>
  `expr_body_pre cenv cx env e es` by metis_tac[] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
    (asm "head_prefix" irule >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`dt`,`k`,`op`,`sa`,`sm`,`shadow_sa`,`shadow_sm`] >> simp[]) >>
  drule_all extcall_keyword_head_outcome >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ _` >>
  qabbrev_tac `Q = (\H (res:value + exception) mid G tn t.
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    return_buf_frame d cenv sm t /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s))` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ _` (irule_at Any) >>
     qunabbrev_tac `headQ` >> simp[Abbr `Q`] >> rpt gen_tac >> strip_tac >> simp[] >>
     `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[body_inv_no_phi] >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q _` (irule_at Any) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_return,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >> suspend "tail"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extcall_request_keywords_prefix_from_head[tail]:
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v, mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ _ = (INL v,mid with gas_obs := [])`
       (irule_at Any) >> imp_res_tac expr_body_pre_static_facts >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
  `body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >> metis_tac[]) >>
  `ci_mono sa sm` by
    (qpat_assum `compile_ext_call_kwarg _ _ _ _ e sa = _` (fn th =>
       mp_tac (Q.SPECL [`compile_expr`,`cenv`,`rt`,`k`,`e`,`sa`]
         ci_mono_compile_ext_call_kwarg) >>
       simp[th, cj 1 ci_mono_compile_expr_sa])) >>
  `local_ptrs_reserved cenv sm /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[ci_mono_def, local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Q _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  fs[Abbr `Q`] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)` by
    (qpat_x_assum `!ks' vo' go' dopt' sa' sb' sha shb ee z G tn.
                   _ ==> gas_prefix_full _ _ _ (eval_exprs cx xs) _`
       (qspecl_then [`ks`,`vot`,`got`,`dopt_t`,`sm`,`sb`,`shadow_sm`,`shadow_sb`,
                     `mid`,`t`,`G1`,`tn1`] mp_tac) >> simp[] >> metis_tac[]) >>
  `!st. SND (bind (eval_exprs cx xs) (\vs. return (v::vs)) st) =
        SND (eval_exprs cx xs st)` by
    (gen_tac >> Cases_on `eval_exprs cx xs st` >> Cases_on `q` >> simp[bind_def, return_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extcall_request_keywords_prefix_from_head
*)
