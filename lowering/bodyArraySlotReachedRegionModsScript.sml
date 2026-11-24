(* Reached array slot geometry after a linked non-reading subscript. *)
Theory bodyArraySlotReachedRegionMods
Ancestors vyperStorageBackend[qualified,ignore_grammar] stmtSimAppendStorageCompose[qualified,ignore_grammar]
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods bodyArrayNoCopyKeyFramesMods
  bodySubscriptArrayRouteDefsMods
  bodyFullSubscriptExprSlotRegion bodyFullSubscriptPopSlotRegion
  bodyFullSubscriptLiveSlotSelect
  accountsRelProps stmtSimAugAssignPlaceStorage vyperStorageFootprint
  loweringPosts exprSimFieldLayout targetSubscriptStorage gasOutcomeFull
  vyperStorageTrace vyperStoragePlaceObserved vyperStoragePlaceRegion
  vyperTypeValues vyperTypeEvalCaseProofs vyperTypeConstantFold
  vyperTypeInvariants vyperPlaceTyping
  bodyAssignNameLinkedSetup bodyFullPostsMods bodyFullPredsMods
  exprBodyPreProps exprSimHypsDefs exprSimSource exprLowering
  vyperTypeEvalSoundness vyperEvalOutcomeSuffix
  vyperInterpreter vyperState vyperAST vyperTypeSystem vyperValue
  vyperTyping vyperTypeCallGraph vyperTypeCallStackSoundness
  compileEnv context words integer list finite_map
Theorem array_reached_eval_sound_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e es = (res,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee /\ no_type_error_result res /\
  (case res of INL raw => eval_result_typed (env,cx,ee) raw (Type (expr_type e))
             | INR _ => T)
Proof
  strip_tac >>
  `IS_SOME ee.outcomes` by
    (irule eval_expr_outcomes_some >> fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all_then assume_tac eval_expr_popped_keys_indexed >>
  qspecl_then [`cx`,`e`] (mp_tac o CONJUNCT1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es`,`res`,`ee`] mp_tac) >>
  simp[] >> strip_tac >>
  `outcomes_accounts_typed ee.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >> fs[outcomes_accounts_typed_def]) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED
Theorem array_slot_root_after_index[local]:
  well_typed_expr env obj /\ runtime_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr obj) /\
  eval_expr cx obj st =
    (INL (PlaceR (StoragePlace tr slot vt)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) =
    (INL key,fin) /\ storage_well_formed_on cx st (FST H) /\
  valid_horizon cx st0 H fin.storage_trace ==>
  ?off root path delta.
    MEM (StorageRoot tr off root) fin.storage_trace /\
    storage_subregion root path delta vt /\ slot = n2w off + n2w delta
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `storage_trace_frame (bind (eval_expr cx idx) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `?xs. fin.storage_trace = mid.storage_trace ++ xs` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule valid_horizon_append >> qexists `xs` >> fs[]) >>
  `storage_observations_ok cx H fin.storage_trace` by fs[valid_horizon_def] >>
  `?off root path delta.
    MEM (StorageRoot tr off root) mid.storage_trace /\
    storage_subregion root path delta vt /\ slot = n2w off + n2w delta` by
    (Q.SUBGOAL_THEN
       `!env' cx' ty bt st' tr' slot' leaf u.
          well_typed_expr env' (Pop ty bt) /\
          runtime_consistent env' cx' st' /\
          regions_consistent (FST H) /\
          storage_locks_separated (FST H) (SND H) /\
          storage_well_formed_on cx' st' (FST H) /\
          functions_well_typed cx' /\
          call_evaluation_safe cx' (int_calls_expr (Pop ty bt)) /\
          storage_observations_ok cx' H u.storage_trace /\
          eval_expr cx' (Pop ty bt) st' =
            (INL (PlaceR (StoragePlace tr' slot' leaf)),u) ==>
          ?off root path delta.
            MEM (StorageRoot tr' off root) u.storage_trace /\
            storage_subregion root path delta leaf /\
            slot' = n2w off + n2w delta` assume_tac
     >- (rpt gen_tac >> strip_tac >>
         metis_tac[subscript_pop_result_slot_region]) >>
     drule (Q.SPEC `H` subscript_expr_result_slot_region_from_pop) >>
     (metis_tac [valid_horizon_def])) >>
  qexistsl [`off`,`root`,`path`,`delta`] >> simp[MEM_APPEND]
QED


Theorem array_slot_reached_region_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (StoragePlace tr slot vt) ==>
  ann = et /\
  ?etv. vt = ArrayTV etv bd /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME vt /\
    well_formed_type_value vt /\
    well_formed_type_value etv /\
    bound_length bd < dimword (:256) /\
    word_scale (slot_loc tr) = 1 /\
    elem_size_in_location cenv (slot_loc tr) et = type_slot_size etv /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      (?off root path delta. MEM (StorageRoot tr off root) fin.storage_trace /\
        storage_subregion root path delta vt /\
        slot = n2w off + n2w delta) /\
      storage_place_observed H (StoragePlace tr slot vt) /\
      storage_read_live H tr (get_storage cx fin tr) slot vt /\
      slots_in_range (get_storage cx fin tr) (w2n slot) vt /\
      w2n slot + type_slot_size vt <= dimword (:256))
Proof
  strip_tac >> drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs1)` by simp[] >>
  drule_all_then strip_assume_tac array_reached_eval_sound_mods >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     simp[] >> metis_tac[env_consistent_type_defs_get_tenv]) >>
  `?etv. vt = ArrayTV etv bd /\
      evaluate_type (get_tenv cx) et = SOME etv /\
      evaluate_type (get_tenv cx) (ArrayT et bd) = SOME vt /\
      well_formed_type_value vt` by
    (gvs[] >>
     drule_then strip_assume_tac evaluate_type_ArrayT_cases >> metis_tac[]) >>
  `ann = et` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `?etv. vt = ArrayTV etv bd /\
      evaluate_type (get_tenv cx) et = SOME etv /\
      evaluate_type (get_tenv cx) (ArrayT et bd) = SOME vt /\
      well_formed_type_value vt /\ well_formed_type_value etv` by
    (drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
     qexists `etv` >> simp[] >>
     qpat_assum `evaluate_type _ et = SOME etv` mp_tac >>
     qpat_assum `evaluate_type _ et = SOME elem_tv` mp_tac >>
     simp[] >> strip_tac >>
     drule_then ACCEPT_TAC evaluate_type_well_formed_type_value) >>
  `bound_length bd < dimword (:256)` by
    metis_tac[target_storage_array_type_bound] >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule assign_name_memory_bytes_mods >>
     goal_assum (drule_at (Pat `evaluate_type _ et = _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  `word_scale (slot_loc tr) = 1 /\
   elem_size_in_location cenv (slot_loc tr) et = type_slot_size etv` by
    (Cases_on `tr` >> simp[slot_loc_def,elem_size_in_location_def,
       word_scale_def,is_slot_addressed_def,
       valueEncodingPropsTheory.type_memory_size_slots,
       arithmeticTheory.ADD_DIV_RWT]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    ?off root path delta. MEM (StorageRoot tr off root) fin.storage_trace /\
      storage_subregion root path delta vt /\ slot = n2w off + n2w delta` by
    (qx_gen_tac `H` >> strip_tac >>
     irule array_slot_root_after_index >>
     qexistsl [`H`,`cx`,`env`,`gs2`,`idx`,`key`,`mid`,`obj`,
               `es with gas_obs := gs1`,`st0`] >>
     simp[] >>
     `runtime_consistent env cx (es with gas_obs := gs1)` by
       (qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` kall_tac >>
        qpat_assum `expr_sim_inv_mods _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
        simp[vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
     `storage_well_formed_on cx (es with gas_obs := gs1) (FST H)` by
       ((qpat_assum `!H. valid_horizon _ _ H _ ==> _`
          (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
        fs[storage_well_formed_on_def,
           vyperStorageBackendTheory.get_storage_def,
           stmtSimAppendStorageComposeTheory.get_storage_gas_obs] >> (metis_tac[storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def, stmtSimAppendStorageComposeTheory.get_storage_gas_obs]))) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     metis_tac[]) >>
  conj_tac >- (metis_tac[]) >>
  qexists `etv` >>
  conj_tac >- (metis_tac[]) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- ((gvs[])) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- (metis_tac[]) >>
     qx_gen_tac `H` >> strip_tac >>
  `storage_place_observed H (StoragePlace tr slot vt)` by
    metis_tac[stmtSimAugAssignPlaceStorageTheory.aug_place_storage_rooted_observed] >>
  `storage_read_live H tr (get_storage cx fin tr) slot vt /\
   slots_in_range (get_storage cx fin tr) (w2n slot) vt` by
    (Cases_on `type_slot_size vt = 0` >-
       (simp[loweringStateRelDefsTheory.storage_read_live_def,
             vyperStorageWritePreservationTheory.zero_slot_size_slots_in_range] >>
        rpt strip_tac >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
        simp[wordsTheory.w2n_lt]) >>
     conj_tac >-
       (metis_tac[accountsRelPropsTheory.storage_place_observed_read_live,
                   arithmeticTheory.NOT_ZERO_LT_ZERO]) >>
     `storage_well_formed_on cx fin (FST H)` by
       metis_tac[array_nocopy_key_prefix_frames_mods] >>
     irule stmtSimAugAssignPlaceStorageTheory.aug_place_observed_slots_in_range >>
     conj_tac >- decide_tac >>
     qexists_tac `H` >> fs[valid_horizon_def]) >>
  `w2n slot + type_slot_size vt <= dimword (:256)` by
    (Cases_on `type_slot_size vt = 0` >-
       simp[arithmeticTheory.LESS_IMP_LESS_OR_EQ, wordsTheory.w2n_lt] >>
     qpat_assum `storage_place_observed H _`
       (strip_assume_tac o PURE_REWRITE_RULE
         [vyperStoragePlaceObservedTheory.storage_place_observed_def]) >>
     rename1 `storage_subregion tv path delta vt` >>
     rename1 `slot = root + n2w delta` >>
     drule_then assume_tac vyperStoragePlaceRegionTheory.storage_subregion_bounds >>
     `w2n root + type_slot_size tv <= dimword (:256)` by
       metis_tac[valid_horizon_def, regions_consistent_def] >>
     gvs[] >>
     `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by
       decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  metis_tac[]
QED
