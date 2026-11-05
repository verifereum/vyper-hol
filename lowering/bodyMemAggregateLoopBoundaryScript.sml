(* Reachability interface for the conditional aggregate children predicate. *)
Theory bodyMemAggregateLoopBoundary
Ancestors
  bodyMemoryPreds gasSummary gasOutcome gasSummaryCompose gasExemptCert vyperState
  exprSimHyps vyperEvalExprPreservesScopesDom vyperImmutableMetadataFrame
  loweringPosts exprSimSource exprLoweringProps compileEnv

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

Theorem aggregate_tuple_ignore_values_mem[local]:
  ignore_bind (bind (eval_exprs cx args) (\vs. return (v::vs))) (return ()) =
  ignore_bind (eval_exprs cx args) (return ())
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >> Cases_on `q` >> simp[]
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
              aggregate_tuple_ignore_values_mem] >>
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

Theorem aggregate_alloca_immutable_sep_mem:
  stmt_state_rel ctx func cenv cx es t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = venomInst$ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
  cenv.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b sz
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> regions_disjoint _ _ b sz` irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aggregate_regions_disjoint_slice:
  regions_disjoint io k b sz /\ off + n <= sz ==>
  regions_disjoint io k (b+off) n
Proof
  simp[regions_disjoint_def] >> decide_tac
QED
