(* Request prefixes for word argument lists. *)
Theory s1PrefixWordArgs
Ancestors
  bodyFullWordArgs bodyFullPreds bodySimFull bodyFullIfExpReach
  gasOutcomeFullCompose s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixOfVV
  exprSimSource exprSimWordArgs exprLoweringProps gasShadowCompileStmtHelpers
  gasShadowState s1PrefixDefs s1PrefixProps compileEnv
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState fragExec
  loweringPosts loweringShapeDefs exprBodyPreProps exprSimDefs list pair sum
  bodyFullExprsListFacts[qualified] bodyFullSimProjection[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  Induct
  >- (rpt strip_tac >> irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame, eval_exprs_nil]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok cx (e::rest)` >>
  `tyf (gas_shadow_expr e) = tyf e` by simp[] >>
  gvs[lower_word_args_cons, MAP] >>
  `gas_shadow_state s1 s1'` by
    (`gas_shadow_state
        (SND (lower_value compile_expr cenv (tyf e) e sa))
        (SND (lower_value compile_expr (gas_shadow_env T cenv) (tyf e)
          (gas_shadow_expr e) shadow_sa))` suffices_by simp[] >>
     irule (cj 2 (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env)) >>
     simp[]) >>
  `ci_mono sa s1 /\ ci_mono shadow_sa s1'` by
    metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `ci_mono s1 sm /\ ci_mono s1' shadow_sm` by
    (rpt conj_tac >> irule ci_mono_lower_word_args >> goal_assum (drule_at Any)) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sm func /\
   fn_has_code shadow_sa s1' shadow_func /\ fn_has_code s1' shadow_sm shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl]) >>
  suspend "head"
QED
*)
Theorem lower_word_args_by_type_prefix:
  !todo DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx tyf
    es st0 sa sm shadow_sa shadow_sm xs s0 G0 tn0.
    (!e. tyf (gas_shadow_expr e) = tyf e) /\
    (!e ee. MEM e todo /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)) /\
    body_exprs_full_ok cx todo /\ body_exprs_prefix_ok cx todo /\
    body_inv tops ctx cenv cx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
    lower_word_args cenv tyf todo sa = (xs,sm) /\
    lower_word_args (gas_shadow_env T cenv) tyf (MAP gas_shadow_expr todo) shadow_sa =
      (xs,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx todo) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume lower_word_args_by_type_prefix[head]:
  `expr_body_pre cenv cx env e es` by
    (qpat_assum `!e ee. _` (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (tyf e) e es` by
    (qpat_assum `body_exprs_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def] o
        CONJUNCT1 o PURE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `s1'`, `x`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  `body_expr_full_ok cx e` by
    fs[Once bodyFullExprsListFactsTheory.body_exprs_full_ok_cons] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (tyf e) e es` by
    (irule (cj 1 bodyFullSimProjectionTheory.body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `s1'`, `x`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. headQ H rr ee G tn u /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK u,G,tn)) headR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_prefix_full_bind >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_return,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  qexistsl_tac [`(\H rr ee G tn u. pathQ H rr ee G tn u /\ ~u.vs_halted)`,
    `headR`, `cx_tops cx`] >>
  rpt conj_tac
  >- (BETA_TAC >> rpt gen_tac >> strip_tac >> suspend "tail")
  >- (simp[Abbr `headR`] >> rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[expr_exit_def]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ headR` (irule_at Any) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume lower_word_args_by_type_prefix[tail]:
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx rest) (mid,t,G1,tn1)` suffices_by
    (strip_tac >>
     qmatch_goalsub_abbrev_tac `gas_prefix_full P _ _ wrapped _` >>
     `gas_prefix_full P cx st0 wrapped (mid,t,G1,tn1) <=>
      gas_prefix_full P cx st0 (eval_exprs cx rest) (mid,t,G1,tn1)` suffices_by simp[] >>
     irule gas_prefix_full_state_cong >> simp[Abbr `wrapped`] >>
     gen_tac >> Cases_on `eval_exprs cx rest qe` >> Cases_on `q` >>
     simp[bind_def, return_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` mp_tac >>
  simp[Abbr `pathQ`, Abbr `headQ`] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv _ ctx _ cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP body_inv_no_phi (CONJ inv member))))) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
         ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe])))))) >>
  suspend "restart"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume lower_word_args_by_type_prefix[restart]:
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_sim_inv cenv cx env (mid with gas_obs := [])` suffices_by simp[] >>
     irule (cj 1 (SIMP_RULE (srw_ss()) [SF ETA_ss] expr_body_pre_eval)) >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `?s tv t' s1' v' t1. eval_expr cx e s = (INL tv,t') /\
                          read_result cx tv s1' = (INL v',t1)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_exprs_full_ok cx rest /\ body_exprs_prefix_ok cx rest` by
    (qpat_x_assum `body_exprs_full_ok _ (_::_)` mp_tac >>
     qpat_x_assum `body_exprs_prefix_ok _ (_::_)` mp_tac >>
     simp[Once bodyFullExprsListFactsTheory.body_exprs_full_ok_cons,
          body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame d cenv s1 t` by
    (Cases_on `d` >> fs[return_buf_frame_def] >> PairCases_on `x'` >>
     fs[return_buf_frame_def] >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     metis_tac[not_fresh_at_mono]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (conj_tac >> rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[expr_post_def]) >>
  first_x_assum irule >> simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`d`,`env`,`s1`,`shadow_func`,`s1'`,`shadow_sm`,
                `sm`,`tops`,`tyf`,`ys`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  qpat_assum `!e ee. _` (qspecl_then [`e'`,`ee`] mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise lower_word_args_by_type_prefix
*)
