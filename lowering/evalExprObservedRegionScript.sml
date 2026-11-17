Theory evalExprObservedRegion
Ancestors
  vyperFiniteStoragePreservation
  list vyperStorageFootprint vyperStorageTrace vyperTypeEvalStoragePreservation
  vyperTypeEvalSoundness vyperTypeSystem vyperTypeExprSoundness
  vyperTypeStmtSoundness vyperTypeCallStackSoundness vyperEvalMisc
  vyperStorageRegionWrite vyperStoragePlaceRegion vyperTypeStoragePreservation
  vyperStorageBackend vyperStoragePlaceProvenance words
  vyperPlaceTyping vyperPlaceFrames vyperPlaceStoragePreservation
  vyperTypeCallGraph vyperInterpreter vyperState vyperValue
  vyperStaticCallFrame vyperReadOnlyCalls
Libs
  wordsLib

(* A successful pop retains a child address. Its pre-pop length must fit
   the observed root's capacity; the post-pop length alone is insufficient. *)
Theorem pop_storage_observed_region[local]:
  regions_consistent regions /\
  storage_well_formed_on cx st regions /\
  MEM (b,n2w offset,root_tv) regions /\
  MEM (StorageRoot b offset root_tv) st.storage_trace /\
  storage_subregion root_tv path delta (ArrayTV elem (Dynamic n)) /\
  base_slot = n2w offset + n2w delta /\
  pop_place cx (StoragePlace b base_slot (ArrayTV elem (Dynamic n))) st =
    (INL (PlaceR (StoragePlace b' slot leaf)),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b' offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  strip_tac >>
  `w2n base_slot = w2n (n2w offset : bytes32) + delta` by
    (irule storage_subregion_offset_no_wrap >> simp[] >>
     qexistsl [`b`,`ArrayTV elem (Dynamic n)`,`path`,`regions`,`root_tv`] >>
     simp[type_slot_size_def]) >>
  `slots_in_range (get_storage cx st b) (w2n base_slot)
     (ArrayTV elem (Dynamic n))` by
    (`slots_in_range (get_storage cx st b)
        (w2n (n2w offset : bytes32)) root_tv` by
       metis_tac[storage_well_formed_on_def] >>
     drule_all storage_subregion_slots_in_range >> simp[]) >>
  `w2n (lookup_storage base_slot (get_storage cx st b)) <= n` by
    gvs[Once vyperLookupStorageTheory.slots_in_range_def,
        vyperStorageTheory.read_slot_def] >>
  `?suffix. st'.storage_trace = st.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_pop_place] >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[NoAsms, pop_place_def, bind_def, ignore_bind_def, get_storage_backend_eq,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> qpat_x_assum `base_slot = _` mp_tac >>
  gvs[] >> disch_tac >>
  qexistsl [`offset`,`root_tv`,
    `path ++ [ValueSubscript (IntV &(w2n (lookup_storage base_slot
       (get_storage cx st b)) - 1))]`,
    `delta + (1 + (w2n (lookup_storage base_slot (get_storage cx st b)) - 1) *
       type_slot_size elem)`] >>
  simp[MEM_APPEND, word_add_n2w, WORD_ADD_ASSOC] >>
  irule storage_subregion_append >>
  goal_assum (drule_at Any) >>
  gvs[storage_subregion_def, word_add_n2w] >> decide_tac
QED

Theorem conditional_result_not_storage_place[local]:
  conditional_result cx result st <>
    (INL (PlaceR (StoragePlace b slot leaf)),st')
Proof
  Cases_on `result` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def, bind_def, return_def, raise_def,
       COND_RATOR, AllCaseEqs()]
QED

Theorem select_result_observed_region[local]:
  (!b slot leaf. pv = PlaceR (StoragePlace b slot leaf) ==>
    ?offset tv path delta.
      MEM (StorageRoot b offset tv) st.storage_trace /\
      storage_subregion tv path delta leaf /\
      slot = n2w offset + n2w delta) /\
  select_result cx ty pv sb st =
    (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  Cases_on `pv` >> simp[select_result_def, bind_def,
    lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> irule (SRULE [] extend_place_observed_region) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem eval_raw_call_not_storage_place[local]:
  eval_raw_call cx flags addr data amount gas st <>
    (INL (PlaceR (StoragePlace b slot leaf)),st')
Proof
  simp[eval_raw_call_def, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, pairTheory.FORALL_PROD, AllCaseEqs()]
QED

Theorem eval_ext_call_not_storage_place[local]:
  eval_ext_call cx static skip sig opts vs st <>
    (INL (PlaceR (StoragePlace b slot leaf)),st')
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, vyperMiscTheory.option_CASE_rator,
       pairTheory.FORALL_PROD, AllCaseEqs()]
QED

Theorem eval_send_not_storage_place[local]:
  eval_send cx gas vs st <>
    (INL (PlaceR (StoragePlace b slot leaf)),st')
Proof
  Cases_on `vs` >> simp[eval_send_def, raise_def] >>
  rename1 `eval_send cx gas (head::tail)` >> Cases_on `tail` >>
  simp[eval_send_def, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, vyperMiscTheory.option_CASE_rator,
       pairTheory.FORALL_PROD, AllCaseEqs()]
QED

Theorem eval_create_not_storage_place[local]:
  vyperCreate$eval_create cx kind salt rof tys vs blueprint_size st <>
    (INL (PlaceR (StoragePlace b slot leaf)),st')
Proof
  simp[vyperCreateTheory.eval_create_def,
       vyperCreateTheory.create_oracle_result_def,
       vyperCreateTheory.create_soft_failure_def,
       bind_def, ignore_bind_def, return_def, raise_def, COND_RATOR,
       vyperMiscTheory.option_CASE_rator, pairTheory.FORALL_PROD, AllCaseEqs()]
QED

Theorem eval_expr_observed_region:
  !e cx st b slot leaf st' env H.
    runtime_consistent env cx st /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx st H st'.storage_trace /\
    eval_expr cx e st = (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
    ?offset tv path delta.
      MEM (StorageRoot b offset tv) st'.storage_trace /\
      storage_subregion tv path delta leaf /\
      slot = n2w offset + n2w delta
Proof
  (* Mapping prefixes are typed as places rather than ordinary expressions. *)
  `!e cx st b slot leaf st' env H.
    runtime_consistent env cx st /\
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx st H st'.storage_trace /\
    eval_expr cx e st = (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
    ?offset tv path delta.
      MEM (StorageRoot b offset tv) st'.storage_trace /\
      storage_subregion tv path delta leaf /\
      slot = n2w offset + n2w delta` suffices_by metis_tac[] >>
  measureInduct_on `expr_size e` >> Cases_on `e` >| [
    suspend "Name", suspend "TopLevelName", suspend "FlagMember",
    suspend "IfExp", suspend "Literal", suspend "StructLit",
    suspend "Subscript", suspend "Attribute", suspend "Builtin",
    suspend "TypeBuiltin", suspend "Pop", suspend "Call"]
QED

Resume eval_expr_observed_region[Name]:
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, ignore_bind_def, raise_def, AllCaseEqs()]
QED

Resume eval_expr_observed_region[TopLevelName]:
  rpt gen_tac >> qmatch_goalsub_rename_tac `eval_expr cx (TopLevelName ty nsid) st` >>
  PairCases_on `nsid` >> pure_once_rewrite_tac[evaluate_def] >>
  metis_tac[lookup_global_observed_region]
QED

Resume eval_expr_observed_region[FlagMember]:
  rpt gen_tac >> qmatch_goalsub_rename_tac `eval_expr cx (FlagMember ty nsid field_id) st` >>
  PairCases_on `nsid` >>
  simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
       lift_option_type_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Resume eval_expr_observed_region[IfExp]:
  simp[Once evaluate_def, bind_def, AllCaseEqs(),
       conditional_result_not_storage_place]
QED

Resume eval_expr_observed_region[Literal]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_expr_observed_region[StructLit]:
  rpt gen_tac >> qmatch_goalsub_rename_tac `eval_expr cx (StructLit ty nsid fields) st` >>
  PairCases_on `nsid` >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()]
QED

Resume eval_expr_observed_region[Builtin]:
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume eval_expr_observed_region[TypeBuiltin]:
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume eval_expr_observed_region[Call]:
  rpt gen_tac >> qmatch_goalsub_rename_tac `eval_expr cx (Call ty target args drv) st` >>
  Cases_on `target` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, pairTheory.FORALL_PROD, AllCaseEqs(),
       eval_raw_call_not_storage_place,
       eval_ext_call_not_storage_place, eval_send_not_storage_place,
       eval_create_not_storage_place]
  >- (qmatch_goalsub_rename_tac `eval_expr cx (Call ty (IntCall nsid) args drv) st` >>
      PairCases_on `nsid` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           vyperMiscTheory.option_CASE_rator, pairTheory.FORALL_PROD,
           AllCaseEqs()]) >>
  qmatch_goalsub_rename_tac `vyperCreate$eval_create cx kind` >> Cases_on `kind` >>
  simp[bind_def, AllCaseEqs(), eval_create_not_storage_place]
QED

Resume eval_expr_observed_region[Attribute]:
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `eval_expr cx (Attribute ty child fld) st` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env child` by gvs[well_typed_expr_def] >>
  `call_evaluation_safe cx (int_calls_expr child)` by
    gvs[int_calls_expr_def] >>
  qpat_x_assum `eval_expr cx (Attribute _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_expr cx child st = (INL child_pv,child_st)` >>
  `?suffix. st'.storage_trace = child_st.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
  `valid_horizon cx st H child_st.storage_trace` by
    gvs[valid_horizon_def, storage_observations_ok_append] >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp_tac (srw_ss()) [vyperASTTheory.expr_size_def] >> strip_tac >>
  irule (SRULE [] select_result_observed_region) >>
  goal_assum (drule_at Any) >> rpt gen_tac >> strip_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume eval_expr_observed_region[Pop]:
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `eval_expr cx (Pop elem_ty bt) st` >>
  qpat_x_assum `!y. _` kall_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env (Pop elem_ty bt)` by
    gvs[well_typed_expr_def] >>
  drule vyperTypeAssignContextTheory.well_typed_expr_Pop_dynamic_target >>
  strip_tac >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    gvs[int_calls_expr_def] >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_target_place cx bt st = (INL p,middle)` >>
  `?suffix. st'.storage_trace = middle.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_pop_place] >>
  `valid_horizon cx st H middle.storage_trace` by
    gvs[valid_horizon_def, storage_observations_ok_append] >>
  `storage_well_formed_on cx middle (FST H)` by
    (irule (cj 8 (SPEC_ALL eval_storage_well_formed_on_mutual)) >>
     fs[valid_horizon_def] >>
     goal_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `well_typed_target _ _ _`)) >> simp[]) >>
  qpat_x_assum `st'.storage_trace = _` kall_tac >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  Cases_on `p` >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
      evaluate_type_def, vyperTypeInvariantsTheory.runtime_place_typed_def,
      AllCaseEqs()]
  >- (drule eval_target_place_observed_region >> strip_tac >>
      irule (SRULE [] pop_storage_observed_region) >>
      goal_assum (drule_at (Pat `pop_place _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
      goal_assum (drule_at (Pat `MEM (StorageRoot _ _ _) _`)) >>
      qexists_tac `FST H` >>
      gvs[valid_horizon_def] >>
      metis_tac[storage_observations_ok_root]) >>
  gvs[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def,
      pairTheory.FORALL_PROD, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >>
  PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]
QED

Resume eval_expr_observed_region[Subscript]:
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `eval_expr cx (Subscript ty child idx) st` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(well_typed_expr env child \/ ?vt. type_place_expr env child = SOME vt)` by
    (qpat_x_assum `well_typed_expr _ _ \/ _` mp_tac >>
     simp[well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  `call_evaluation_safe cx (int_calls_expr child)` by
    (qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[int_calls_expr_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  Cases_on `subscript_reads_base cx child idx`
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
          return_def, raise_def, AllCaseEqs()]) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  qmatch_assum_rename_tac `eval_expr cx child st = (INL child_pv,child_st)` >>
  qmatch_assum_rename_tac `eval_expr cx idx child_st = (INL idx_pv,idx_st)` >>
  `?suffix. st'.storage_trace = idx_st.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
  `?prefix. idx_st.storage_trace = child_st.storage_trace ++ prefix` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `valid_horizon cx st H child_st.storage_trace` by
    gvs[valid_horizon_def, storage_observations_ok_append] >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp_tac (srw_ss()) [vyperASTTheory.expr_size_def] >> strip_tac >>
  irule (SRULE [] select_result_observed_region) >>
  goal_assum (drule_at Any) >> rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac
    `eval_expr cx child st = (INL (PlaceR (StoragePlace child_b child_slot child_leaf)),child_st)` >>
  qpat_x_assum `!cx. _` (qspecl_then
    [`cx`,`st`,`child_b`,`child_slot`,`child_leaf`,`child_st`,`env`,`H`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl [`offset`,`tv`,`path`,`delta`] >> simp[MEM_APPEND]
QED

Finalise eval_expr_observed_region
