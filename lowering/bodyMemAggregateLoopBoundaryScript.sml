(* Reachability interface for the conditional aggregate children predicate. *)
Theory bodyMemAggregateLoopBoundary
Ancestors
  exprSimAggregateLoops
  bodyMemoryPreds gasSummary gasOutcome gasSummaryCompose gasExemptCert vyperState
  exprSimHyps vyperEvalExprPreservesScopesDom vyperImmutableMetadataFrame
  loweringPosts exprSimSource exprLoweringProps compileEnv
  fragGasMode fragGasPathMem exprSimMemDefs exprSimWordArgs
  exprLowering vyperInterpreter exprSimProps

Theorem aggregate_body_exprs_mem_tail:
  body_exprs_mem_ok cx (e::args) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s)
    marks (INL tv) ee (OK r) /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (ee,r)
    [] (INL v) ee' (OK q) ==>
  body_exprs_mem_ok cx args
Proof
  simp[body_exprs_mem_ok_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  first_x_assum irule >>
  metis_tac[]
QED

Theorem aggregate_tuple_bind_outcome_any:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!marks v ee t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    ee.gas_obs = [] /\ P v ee t ==>
    gas_outcome memory tops (ctx,func)
      (k v : evaluation_state -> value list evaluation_result) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[] >>
      first_x_assum (qspecl_then [`left`, `v`, `es_end with gas_obs := []`, `t`] mp_tac) >>
      (impl_tac >- fs[gas_marked_exec_def]) >>
      rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists_tac `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal])
      >- (qexists_tac `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal]) >>
      qexists_tac `left ++ right` >> disj2_tac >>
      rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
      irule_at Any gasExemptCertTheory.gas_exempt_cert_bind_result >>
      simp[GSYM ignore_bind_def] >> metis_tac[])
  >- (gvs[] >> qexists_tac `left` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_exception]) >>
  qexists_tac `left` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem aggregate_tuple_value_bind_any:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func)
    (k v : evaluation_state -> value list evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `right` strip_assume_tac))
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal])
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  qexists_tac `left ++ right` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_bind_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem aggregate_tuple_values_outcome_any:
  gas_outcome memory tops (ctx,func) (eval_exprs cx args) (es,s) Q1 R1 /\
  (!res ee r. Q1 res ee r ==>
     Q (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) /\
  (!res ee r. R1 res ee r ==>
     R (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es,s) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def,
              aggregate_tuple_ignore_values] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `OK t`] >>
      qpat_x_assum `!res ee r. Q1 _ _ _ ==> _` drule >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def])
  >- (disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `r`] >>
      qpat_x_assum `!res ee r. R1 _ _ _ ==> _` drule >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def]) >>
  disj2_tac >> metis_tac[]
QED

Theorem aggregate_tuple_marked_child_source_any:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK t) ==>
  expr_sim_inv ce cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  immutable_metadata_frame es (mid with gas_obs := []) /\
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,mid with gas_obs := []) tv (Type (expr_type e)) /\
    (!v. read_result cx tv (mid with gas_obs := []) =
           (INL v,mid with gas_obs := []) ==> value_has_type tvt v)
Proof
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
  drule vyperImmutableMetadataFrameTheory.eval_expr_immutable_metadata_frame >>
  simp[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
  metis_tac[]
QED

Theorem aggregate_tuple_marked_footprint_any:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK t) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b n) ==>
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b n)
Proof
  strip_tac >> drule_all aggregate_tuple_marked_child_source_any >> strip_tac >>
  rpt strip_tac >>
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target`
  >- (fs[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
      qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
        (qspec_then `cx.txn.target` mp_tac) >> simp[]) >>
  gvs[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME old` >>
  qpat_x_assum `!addr imms imms' src id. _`
    (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
  Cases_on `FLOOKUP (get_source_immutables ce.ce_module old) name` >>
  simp[] >>
  rename1 `FLOOKUP (get_source_immutables ce.ce_module old) name = SOME entry` >>
  PairCases_on `entry` >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem aggregate_regions_disjoint_slice:
  regions_disjoint io k b sz /\ off + n <= sz ==>
  regions_disjoint io k (b+off) n
Proof
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem aggregate_tuple_nil_outcome_mem:
  ~s.vs_halted /\ Q (INL []) (es with gas_obs := []) s ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx []) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, exprSimWordArgsTheory.eval_exprs_nil,
       gas_marked_path_def] >>
  irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem aggregate_tuple_child_outcome_mem:
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx (e::args) /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func ce cx (expr_type e) e es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  fs[expr_vv_sim_mem_def]
QED

Theorem aggregate_mem_tuple_cons_compile:
  compile_make_tuple compile_expr ce (e::args) buf off sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),st) /\
    compile_make_tuple compile_expr ce args buf
      (off + type_memory_bytes ce (expr_type e)) st = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aggregate_mem_tuple_local_region_backward:
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  conj_tac
  >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`sa`, `es1.scopes`, `s1`] >> gvs[vv_post_def]
QED
