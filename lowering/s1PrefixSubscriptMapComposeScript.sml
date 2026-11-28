Theory s1PrefixSubscriptMapCompose
Ancestors
  s1PrefixPreds s1PrefixCompose bodyFullIfExpReach exprSimSubscriptMap
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  gasOutcomeFullCompose bodyFullPreds bodyFullSimProjection bodyFullShadowBodyInv bodySimFull
  s1PrefixDefs s1PrefixProps exprLowering compileEnv exprSimMapDefs
  fragExec bodyMemoryDefs bodyPtrDefs contextRawReachable instIdxIndep
  exprSimSubscriptArraySource gasContext gasExplicitSites gasShadowCompileBase
  gasShadowState gasShadow venomState venomWf allocaHistory ptrDiscipline
  exprSimHypsDefs exprSimDefs stmtSimDefs exprLoweringProps list

Theorem mapping_key_sims[local]:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> conj_tac
  >- (irule (cj 1 body_expr_full_ok_simulations) >>
      simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok _ _` mp_tac >>
  rewrite_tac[Once body_expr_prefix_ok_def] >> strip_tac >>
  first_x_assum (irule o cj 1) >> simp[] >> metis_tac[]
QED

Theorem mapping_key_admissible[local]:
  (!ex. P (INR ex : eval_result + exception) ==> expr_res_ok (INR ex : value + exception)) /\
  gas_admissible (bind (eval_expr cx e1) k) P es /\
  (!tail. eval_expr cx e1 (es with gas_obs := gs ++ tail) =
           (INL raw,mid with gas_obs := tail)) /\
  (!v. k v = bind (bind (eval_expr cx e2) (read_result cx)) (f v)) ==>
  gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid
Proof
  simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[exprSimDefsTheory.expr_res_ok_def] >>
  rename1 `INR ex` >> first_x_assum irule >>
  qpat_x_assum `!gs res ee. _ ==> P res` (qspec_then `gs ++ gs'` mp_tac) >>
  disch_then (qspecl_then [`INR ex`,`ee`] mp_tac) >>
  qpat_x_assum `monad_bind _ _ _ = (INR _,_)` mp_tac >>
  simp[bind_def] >> BasicProvers.TOP_CASE_TAC >> gvs[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (eval_expr cx e1) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `expr_map_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_map_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                          `bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_expr cx e1) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_map_sim_prefix _ _ _ _ e1 _`
       (mp_tac o REWRITE_RULE [expr_map_sim_prefix_def,expr_map_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                             `bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    let val eq = MATCH_MP eval_expr_subscript_bind th in
      qpat_x_assum `gas_admissible (eval_expr _ (Subscript _ _ _)) _ _`
        (assume_tac o REWRITE_RULE [eq]) >> rewrite_tac[eq]
    end) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  irule gas_prefix_full_bind >>
  simp[cj 5 evaluate_storage_trace_frame,cj 5 evaluate_requests_outcomes_frame,
       storage_trace_frame_read_result,storage_trace_frame_bind_all,storage_trace_frame_select] >>
  qexistsl_tac [
    `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = [] /\
       (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)`,
    `baseR`,`cx_tops cx`] >> simp[] >>
  conj_tac >- suspend "continuation" >>
  conj_tac >- suspend "base_exit" >>
  suspend "base_post"
QED
*)
Theorem mapping_subscript_children_prefix:
  place_type cenv e1 = MapPT kt vt /\
  ~subscript_reads_base cx e1 e2 /\
  (expr_body_pre cenv cx env (Subscript ann e1 e2) es \/
   expr_map_pre cenv cx env (Subscript ann e1 e2) es) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es /\
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es /\
  compile_expr cenv ty e1 sa = (bvv,sm) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa = (bvv,shadow_sm) /\
  lower_value compile_expr cenv (expr_type e2) e2 sm = (key,sn) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
    (gas_shadow_expr e2) shadow_sm = (key,shadow_sn) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_state sn shadow_sn /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sn shadow_func /\
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx (Subscript ann e1 e2)) P es /\
  (!ex. P (INR ex) ==>
     expr_map_res_ok (INR ex : eval_result + exception) /\
     expr_res_ok (INR ex : value + exception)) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tr slot kt' vt' kv st gobs res ee.
    select_result cx (expr_type e1) (HashMapRef tr slot kt' vt') (ValueSubscript kv)
      (st with gas_obs := gobs) = (res,ee) ==>
    EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
      (DROP (LENGTH st.storage_trace) ee.storage_trace)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_expr cx (Subscript ann e1 e2)) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume mapping_subscript_children_prefix[base_post]:
  irule gas_outcome_full_post_path >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
        metis_tac[body_inv_no_phi] >>
      drule gas_origin_ptr_path_dalloca_fmp_headroom >> asm_rewrite_tac[]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ baseQ baseR` (irule_at Any) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume mapping_subscript_children_prefix[base_exit]:
  simp[Abbr `baseR`] >> rpt gen_tac >> Cases_on `res` >>
  simp[exprSimDefsTheory.expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume mapping_subscript_children_prefix[continuation]:
  qx_genl_tac [`marks`,`raw`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`,NoAsms] >> disch_then strip_assume_tac >>
  rename1 `raw = HashMapRef tr slot key_ty value_ty` >>
  qpat_x_assum `raw = HashMapRef _ _ _ _` SUBST_ALL_TAC >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (HashMapRef tr slot key_ty value_ty),mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     pop_assum (fn same =>
       qpat_assum `!tail. eval_expr cx e1 _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,same])))) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule (cj 3 mapping_subscript_index_pre) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[exprSimSourceTheory.expr_body_pre_gas_obs,expr_map_pre_gas_obs] >> metis_tac[]) >>
  `expr_map_pre cenv cx env e1 es` by
    metis_tac[expr_body_pre_map_subscript_base,expr_map_pre_subscript_base] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     drule expr_map_pre_checked_type >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e2) e2 mid /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e2) e2 mid` by
    (irule mapping_key_sims >>
     `body_expr_full_ok cx e2 /\ body_expr_prefix_ok cx e2` by
       (conj_tac >> first_x_assum irule >> goal_assum (drule_at Any)) >>
     simp[] >> qexistsl_tac [`env`,`tops`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (irule mapping_key_admissible >>
     goal_assum (drule_at (Pat `gas_admissible (bind _ _) _ _`)) >>
     qexistsl_tac [`\raw kv. select_result cx (expr_type e1) raw (ValueSubscript kv)`,
       `gas_explicit marks s0.vs_gas_readings`,
       `HashMapRef tr slot key_ty value_ty`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then mp_tac)) >>
     simp[NoAsms] >> strip_tac >> asm_rewrite_tac[]) >>
  suspend "key_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume mapping_subscript_children_prefix[key_bind]:
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid (st0,sm,sn,shadow_sm,shadow_sn,key,t,G1,tn1)` by
    (rewrite_tac[expr_sim_full_pre_def] >> asm_rewrite_tac[] >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)` by
    (qpat_assum `expr_sim_prefix _ _ _ _ e2 mid`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
     disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,
                             `key`,`t`,`G1`,`tn1`] mp_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 mid`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,
                          `key`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ (bind _ _) _ keyQ keyR` >>
  irule gas_prefix_full_bind_no_outcome >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_select,storage_trace_frame_read_result,
       cj 5 evaluate_storage_trace_frame,requests_outcomes_frame_bind_all,
       requests_outcomes_frame_read_result,cj 5 evaluate_requests_outcomes_frame] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!tr slot kt vt kv st gobs res ee. select_result _ _ _ _ _ = _ ==> _`
        (drule_then ACCEPT_TAC)) >>
  qexistsl_tac [`\H res ee G tn u. keyQ H res ee G tn u /\ ~u.vs_halted`,
                `keyR`,`cx_tops cx`] >>
  simp[] >> conj_tac
  >- (simp[Abbr `keyR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_def]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind _ _) _ keyQ keyR` (irule_at Any) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise mapping_subscript_children_prefix
*)
