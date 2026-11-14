(*
 * Statement targets over the finite-horizon joint judgment: a base target
 * (a local, a module variable, a field or an element of one) resolves to
 * its place and its pointer at one joint endpoint, as expr_sim_full's
 * expression resolves to its value.  targetPlaceSimDefs' target_sim and
 * bodyPtrPopTargetDefs' target_sim_ptr over gas_outcome_full, with the
 * shadow compilation and the initial resources of expr_sim_full.
 *
 * The judgments are bodyFullTargetDefs'.
 *
 * TOP-LEVEL:
 *   body_target_sim_full, body_target_place_sim_full -- a target meeting
 *     target_pre whose indices have their joint judgments has both
 *)
Theory bodyFullTarget
Ancestors
  bodyFullTargetRoots bodyFullTargetAttribute bodyFullTargetSubscript
  bodyFullTargetArray bodyFullTargetMapping bodyFullTargetDefs bodyFullPreds
  bodySimFull gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr
  gasExemptCert gasContext targetPlaceSimCasesBase targetPlaceSimCases
  targetPlaceSim targetPlaceSimDefs targetLocalLive vyperLocalAccessFrame
  loweringPosts bodyPtrPopTargetFragTransport
  vyperStorageTrace vyperTypeEnv vyperTypeSystem vyperInterpreter vyperState
  vyperAST pair list exprSimDefs exprSimHypsDefs vyperStorageFootprint

val _ = Parse.hide "body";

(* The element suffix exists for both kinds of subscriptable base; any
   other base has no subscript type. *)
Theorem subscript_tail_full_ok[local]:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  strip_tac >> Cases_on `type_place_target env bt`
  >- simp[subscript_tail_full_def] >>
  rename1 `SOME bvt` >> Cases_on `bvt`
  >- (rename1 `Type ty` >> Cases_on `?et bd. ty = ArrayT et bd`
      >- (gvs[] >> irule target_array_tail_full >> metis_tac[]) >>
      simp[subscript_tail_full_def, type_place_target_SubscriptTarget] >>
      rpt strip_tac >> gvs[] >> Cases_on `ty` >> gvs[subscript_vtype_def]) >>
  irule target_mapping_tail_full >> metis_tac[]
QED

Theorem body_target_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >> irule target_name_sim_full >> simp[])
  >- (PairCases_on `nsid` >> rpt strip_tac >>
      irule target_toplevel_sim_full >> simp[])
  >- (strip_tac >> rpt gen_tac >> strip_tac >>
      `body_base_target_full_ok cx bt` by fs[body_base_target_full_ok_def] >>
      `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
      `target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx env bt es` by metis_tac[] >>
      `subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx env bt e es` by metis_tac[subscript_tail_full_ok] >>
      irule target_subscript_sim_full >> simp[] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `body_base_target_full_ok cx bt` by fs[body_base_target_full_ok_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx env bt es` by metis_tac[] >>
  irule target_attribute_sim_full >> simp[]
QED

(* The place judgment from the base one: eval_target_place is
   eval_base_place then get_place, which runs no instruction; a memory place
   is live in the local's current value (targetLocalLive). *)
Theorem body_target_place_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  rpt strip_tac >>
  drule_all body_target_sim_full >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `shadow_ctx`, `func`,
                           `shadow_func`] assume_tac) >>
  simp[target_place_sim_full_def, eval_target_place_as_bind] >>
  rpt gen_tac >> strip_tac >>
  drule get_place_base_admissible >> strip_tac >>
  qpat_x_assum `target_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `Type ty`, `sa`, `sb`, `shadow_sa`,
                           `shadow_sb`, `r`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> rename1 `get_place pv` >> Cases_on `pv` >>
      simp[get_place_def, storage_trace_frame_return,
           storage_trace_frame_raise]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "place" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def] >>
  metis_tac[expr_exit_INR_retype]
QED

Resume body_target_place_sim_full[place]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `pv` >> simp[] >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv, mid)`
    by (qpat_assum `!tail. eval_base_place _ _ _ = _`
          (qspec_then `[]` mp_tac) >> REWRITE_TAC [APPEND_NIL] >>
        qpat_assum `mid with gas_obs := [] = mid` (fn th => REWRITE_TAC [th])) >>
  `?p. pv = PlaceR p` by
    (Cases_on `pv` >> simp[] >>
     qpat_x_assum `gas_admissible (bind _ get_place) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def, get_place_def, raise_def, target_place_res_ok_def]) >>
  gvs[get_place_def] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `mid`, `INL p`, `t`, `tn1`] >>
  conj_tac >- simp[return_def] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
  strip_tac >> simp[gas_origin_ptr_path_rules] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "live"
QED

Resume body_target_place_sim_full[live]:
  `target_root bt = NameTarget id` by
    metis_tac[target_base_memory_root_ptr] >>
  `target_pre cenv cx env bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    fs[target_pre_def] >>
  drule_all local_base_place_live >> strip_tac >> gvs[] >>
  metis_tac[]
QED
