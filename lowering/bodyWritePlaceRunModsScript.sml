(* One linked target induction, then consume the base result without adding
   instructions or changing its counted execution endpoint. *)
Theory bodyWritePlaceRunMods
Ancestors
  bodyWriteOrdinaryRootMods bodyWriteImmutableRootMods bodyWriteFieldStageMods
  bodyWriteArrayStageMods bodyWriteMapStageMods bodyWriteSubscriptSourceMods
  bodyPtrPopTargetFragTransport gasOutcomeFullBindMods gasOutcomeFullPostMods
  constSubstCorrect targetPlaceSim vyperTypeEnv vyperTypeSystem allocLimits
  targetPlaceSimCasesBase supportedExprs bodyFullPredsMods exprSimHypsDefs
  bodyWriteTargetStageMods bodyFullPostsMods bodyInvSplit gasExemptCertMods
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  exprSimDefs loweringPosts fragGasOriginPtr gasOutcomeFull gasSummary gasOutcome
  gasContext targetPlaceSimCases list bodyFullTargetSubscript bodyWritePlaceLiveMods
Libs
  monadsyntax pairLib

Theorem write_subscript_base_type[local]:
  IS_SOME (type_place_target env (SubscriptTarget bt e)) ==>
  (?ety bd. type_place_target env bt = SOME (Type (ArrayT ety bd))) \/
  (?kt vt. type_place_target env bt = SOME (HashMapT kt vt))
Proof
  Cases_on `type_place_target env (SubscriptTarget bt e)` >- simp[] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[type_place_target_SubscriptTarget] >> strip_tac >>
  Cases_on `vt'` >> gvs[] >> Cases_on `t` >> gvs[subscript_vtype_def]
QED

Theorem write_target_base_run_mods[local]:
  !bt.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    IS_SOME (type_place_target env bt) /\ alloc_limits_target cenv bt /\
    (!e st. MEM e (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
            expr_body_pre_mods mods cenv cx env e st) /\
    body_base_target_full_ok_mods mods exps cx bt /\
    (immutable_root cx bt ==>
       ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
          cenv.ce_is_ctor /\
          FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)) ==>
    write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env bt es
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> irule write_local_root_stage_mods >> qexists_tac `mods` >> simp[])
  >- (rename1 `TopLevelNameTarget key` >> PairCases_on `key` >> strip_tac >>
      Cases_on `immutable_root cx (TopLevelNameTarget (key0,key1))`
      >- (qpat_x_assum `immutable_root _ _ ==> _` drule >>
          simp[target_root_def] >> strip_tac >>
          irule write_immutable_root_stage_mods >> simp[] >>
          qexists_tac `mods` >> simp[]) >>
      irule write_toplevel_ordinary_root_stage_mods >> simp[] >>
      qexists_tac `mods` >> simp[])
  >- (strip_tac >> strip_tac >>
      drule_then strip_assume_tac type_place_target_subscript_child >>
      `write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx env bt es` by
        (first_x_assum irule >>
         simp[alloc_limits_expr_def, target_indices_def, immutable_root_def,
              target_root_def, body_base_target_full_ok_mods_def] >>
         fs[alloc_limits_expr_def, target_indices_def, immutable_root_def,
            target_root_def, body_base_target_full_ok_mods_def] >>
         metis_tac[]) >>
      drule_then strip_assume_tac write_subscript_base_type
      >- (irule write_array_index_stage_mods >> simp[] >>
          qexistsl_tac [`exps`,`mods`,`src`,`tops`] >> simp[]) >>
      irule write_map_index_stage_mods >> simp[] >>
      qexistsl_tac [`exps`,`mods`,`src`,`tops`] >> simp[])
  >> strip_tac >> strip_tac >>
  drule_then assume_tac type_place_target_attribute_child >>
  `write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx env bt es` by
    (first_x_assum irule >>
     fs[alloc_limits_expr_def, target_indices_def, immutable_root_def,
        target_root_def, body_base_target_full_ok_mods_def] >>
     first_assum ACCEPT_TAC) >>
  irule write_field_stage_mods >> simp[] >> reverse conj_tac
  >- (qexists_tac `mods` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  `!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st` by fs[target_indices_def] >>
  drule_all_then strip_assume_tac write_base_reached_source_mods >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ mid`
    (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]
QED

Theorem write_base_to_place_mods[local]:
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  (!gs id path mid ty r G t.
     type_place_target env bt = SOME (Type ty) /\
     eval_base_place cx bt (es with gas_obs := gs) =
       (INL (PlaceR (MemoryPlace id path)),mid) /\
     write_target_location_mods cenv cx bt mid (PlaceR (MemoryPlace id path))
       (Type ty) r G t ==>
     ?entry v. lookup_scopes id mid.scopes = SOME entry /\
               evaluate_subscripts entry.type entry.value path = INL v) ==>
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es
Proof
  strip_tac >> simp[write_place_sim_mods_def, eval_target_place_as_bind] >>
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac get_place_base_admissible >>
  qpat_x_assum `write_base_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_base_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`Type ty`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,
                           `r`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_get_place] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "place" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >>
  conj_tac
  >- (qpat_assum `expr_exit (INR _) _`
        (MATCH_ACCEPT_TAC o MATCH_MP bodyFullTargetSubscriptTheory.expr_exit_INR_retype)) >>
  fs[halt_exit_def]
QED

Resume write_base_to_place_mods[place]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `pv` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL pv,mid)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _`
      (qspec_then `[]` mp_tac) >> REWRITE_TAC[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => REWRITE_TAC[th])) >>
  `?p. pv = PlaceR p` by
    (Cases_on `pv` >> simp[] >>
     qpat_assum `gas_admissible (bind _ get_place) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def, get_place_def, raise_def, target_place_res_ok_def]) >>
  gvs[get_place_def] >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G1`,`mid`,`INL p`,`t`,`tn1`] >>
  conj_tac >- simp[return_def] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  simp[gas_origin_ptr_path_rules] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_assum `!H'. valid_horizon _ _ H' mid.storage_trace ==> _`
    (qspec_then `H` (drule_then assume_tac)) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_assum `!gs id path mid r G t. _ /\ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Finalise write_base_to_place_mods

Theorem write_target_place_run_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env bt = SOME (Type ty) /\ alloc_limits_target cenv bt /\
  (!e st. MEM e (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env e st) /\
  body_base_target_full_ok_mods mods exps cx bt /\
  (immutable_root cx bt ==>
     ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
        cenv.ce_is_ctor /\
        FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)) ==>
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es
Proof
  strip_tac >> irule write_base_to_place_mods >> reverse conj_tac
  >- (irule write_target_base_run_mods >> simp[] >>
      qexistsl_tac [`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule write_place_memory_live_mods >>
  qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `write_target_location_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`mods`,`env`] >> simp[]
QED
