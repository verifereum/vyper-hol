(* Reachability interface for the conditional aggregate children predicate. *)
Theory bodyMemAggregateLoopBoundary
Ancestors
  exprSimAggregateLoops
  bodyMemoryPreds gasSummary gasOutcome gasSummaryCompose gasExemptCert vyperState
  exprSimHyps vyperEvalExprPreservesScopesDom vyperImmutableMetadataFrame
  loweringPosts exprSimSource exprLoweringProps compileEnv loweringStateRelDefs
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

(* Preserve the source typing independently of the declared destination type. *)
Theorem aggregate_tuple_marked_child_declared_source_any:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK t) /\
  arg_type_fits (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv ==>
  expr_sim_inv ce cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  immutable_metadata_frame es (mid with gas_obs := []) /\
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,mid with gas_obs := []) tv (Type (expr_type e)) /\
    (!v. read_result cx tv (mid with gas_obs := []) =
           (INL v,mid with gas_obs := []) ==>
      value_has_type tvt v /\ value_has_type dtv v /\ val_wf dtv v)
Proof
  strip_tac >> drule_all aggregate_tuple_marked_child_source_any >> strip_tac >>
  simp[] >> rpt strip_tac >>
  metis_tac[CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type,
            CONJUNCT1 valueEncodingTypingTheory.value_has_type_val_wf]
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

Theorem aggregate_tuple_child_outcome_mem:
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx (e::args) /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_expr cx e) (es,s0)
    (\H res ee t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func ce cx (expr_type e) e es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then irule >> simp[]
QED

Theorem aggregate_mem_tuple_local_region_backward:
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel H ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post H ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  conj_tac
  >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`sa`, `es1.scopes`, `s1`] >> gvs[vv_post_def]
QED
