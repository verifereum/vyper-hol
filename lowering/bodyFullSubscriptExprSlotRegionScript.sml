(* Source provenance of an expression's returned storage place. *)
Theory bodyFullSubscriptExprSlotRegion
Ancestors
  vyperFiniteStoragePreservation vyperStoragePlaceProvenance
  vyperStoragePlaceRegion vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperCallFrame vyperLocalAccessFrame vyperAST vyperMisc words list pair
Libs
  pairLib

(* For a mapping leaf the select itself records the root. For an ordinary
   storage place it extends the existing capacity path. *)
Theorem select_storage_observed_region[local]:
  (!tr slot leaf. r = PlaceR (StoragePlace tr slot leaf) ==>
    ?off root path delta.
      MEM (StorageRoot tr off root) st.storage_trace /\
      storage_subregion root path delta leaf /\
      slot = n2w off + n2w delta) /\
  select_result cx ty r sb st = (INL (PlaceR (StoragePlace tr slot leaf)),u) ==>
  ?off root path delta.
    MEM (StorageRoot tr off root) u.storage_trace /\
    storage_subregion root path delta leaf /\
    slot = n2w off + n2w delta
Proof
  Cases_on `r` >>
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp[extend_place_def, bind_def, return_def, AllCaseEqs(),
           extend_memory_place_def] >> rpt strip_tac >>
      gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs(),
          extend_memory_place_def] >>
      drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
      `?xs. u.storage_trace = st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, storage_trace_frame_extend_storage] >>
      drule_all storage_subregion_append >> strip_tac >>
      goal_assum (drule_at Any) >> simp[MEM_APPEND] >>
      metis_tac[word_add_n2w, WORD_ADD_ASSOC, WORD_ADD_COMM]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  simp[value_type_CASE_rator, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[record_storage_event_def, return_def, AllCaseEqs()] >>
  qexistsl [`w2n (hashmap_slot c (encode_hashmap_key t v'))`, `leaf`, `[]`, `0`] >>
  simp[storage_subregion_def, WORD_ADD_0]
QED

Theorem subscript_expr_result_slot_region_from_pop:
  !H.
    (!env cx ty bt st tr slot leaf u.
       well_typed_expr env (Pop ty bt) /\
       runtime_consistent env cx st /\
       regions_consistent (FST H) /\
       storage_locks_separated (FST H) (SND H) /\
       storage_well_formed_on cx st (FST H) /\
       functions_well_typed cx /\
       call_evaluation_safe cx (int_calls_expr (Pop ty bt)) /\
       storage_observations_ok cx H u.storage_trace /\
       eval_expr cx (Pop ty bt) st = (INL (PlaceR (StoragePlace tr slot leaf)),u) ==>
       ?off root path delta.
         MEM (StorageRoot tr off root) u.storage_trace /\
         storage_subregion root path delta leaf /\
         slot = n2w off + n2w delta) ==>
    !e env cx st tr slot leaf u.
      (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
      runtime_consistent env cx st /\
      regions_consistent (FST H) /\
      storage_locks_separated (FST H) (SND H) /\
      storage_well_formed_on cx st (FST H) /\
      functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      storage_observations_ok cx H u.storage_trace /\
      eval_expr cx e st = (INL (PlaceR (StoragePlace tr slot leaf)),u) ==>
      ?off root path delta.
        MEM (StorageRoot tr off root) u.storage_trace /\
        storage_subregion root path delta leaf /\
        slot = n2w off + n2w delta
Proof
  gen_tac >> disch_tac >> measureInduct_on `expr_size e` >>
  Cases_on `e` >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- (rename1 `TopLevelName ann nsid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def] >> rpt strip_tac >>
      irule eval_base_place_observed_region >>
      qexistsl [`TopLevelNameTarget (nsid0,nsid1)`, `cx`, `st`] >>
      simp[Once evaluate_def])
  >- (rename1 `FlagMember ann nsid mid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_flag_mem_def, bind_def,
           vyperMiscTheory.option_CASE_rator, lift_option_type_def,
           return_def, raise_def, AllCaseEqs()])
  >- suspend "ifexp"
  >- simp[Once evaluate_def, return_def]
  >- (rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >- suspend "subscript"
  >- suspend "attribute"
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- suspend "pop"
  >> suspend "call"
QED

Resume subscript_expr_result_slot_region_from_pop[ifexp]:
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `conditional_result _ _ _ = _` mp_tac >>
  rename1 `conditional_result cx raw mid = _` >>
  Cases_on `raw` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  simp[conditional_result_def, bind_def, return_def, AllCaseEqs()] >>
  simp[COND_RATOR, bind_def, return_def, AllCaseEqs()]
QED

Resume subscript_expr_result_slot_region_from_pop[pop]:
  rename1 `Pop ann bt` >>
  `!env. type_place_expr env (Pop ann bt) = NONE`
    by simp[Once well_typed_expr_def] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume subscript_expr_result_slot_region_from_pop[call]:
  rename1 `Call ann dest es dflt` >>
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `dest` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac
  >~ [`IntCall nsid`] >-
    (PairCases_on `nsid` >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
         raise_def, UNCURRY, AllCaseEqs()])
  >~ [`eval_send`] >- (drule eval_send_success_value >> simp[])
  >~ [`eval_ext_call`] >- (drule eval_ext_call_success_value >> simp[])
  >~ [`eval_raw_call`] >- (drule eval_raw_call_success_value >> simp[])
  >~ [`eval_raw_call`] >- (drule eval_raw_call_success_value >> simp[]) >>
  drule eval_create_operands_success_value >> simp[]
QED

Resume subscript_expr_result_slot_region_from_pop[attribute]:
  rename1 `Attribute ann obj fld` >>
  `!env. type_place_expr env (Attribute ann obj fld) = NONE`
    by simp[Once well_typed_expr_def] >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `!env cx ty bt st tr slot leaf u. _` kall_tac >>
  gvs[] >>
  `well_typed_expr env obj /\ call_evaluation_safe cx (int_calls_expr obj)` by
    (qpat_x_assum `well_typed_expr env (Attribute _ _ _)` mp_tac >>
     qpat_x_assum `call_evaluation_safe cx _` mp_tac >>
     simp[Once well_typed_expr_def, int_calls_expr_def]) >>
  drule_at (Pos last) select_storage_observed_region >>
  disch_then irule >> rpt gen_tac >> disch_tac >> gvs[] >>
  `storage_observations_ok cx H s''.storage_trace` by
    (`?xs. u.storage_trace = s''.storage_trace ++ xs` by
       metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
     fs[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `obj` mp_tac) >>
  simp[expr_size_def] >> metis_tac[]
QED

Resume subscript_expr_result_slot_region_from_pop[subscript]:
  rename1 `Subscript ann obj idx` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `!env cx ty bt st tr slot leaf u. _` kall_tac >>
  Q.SUBGOAL_THEN
    `well_typed_expr env obj \/ ?vt. type_place_expr env obj = SOME vt` assume_tac
  >- (qpat_x_assum `well_typed_expr env (Subscript _ _ _) \/ _` strip_assume_tac
      >- (pop_assum mp_tac >> simp[Once well_typed_expr_def] >> metis_tac[]) >>
      pop_assum mp_tac >> simp[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `well_typed_expr env (Subscript _ _ _) \/ _` kall_tac >>
  `call_evaluation_safe cx (int_calls_expr obj)` by
    metis_tac[int_calls_expr_def, call_evaluation_safe_append_left] >>
  qpat_x_assum `?v mid. eval_expr cx obj st = (v,mid) /\ _` strip_assume_tac >>
  gnvs[] >>
  drule_at (Pos last) select_storage_observed_region >> disch_then irule >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `(if subscript_reads_base _ _ _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >> gnvs[] >>
  rename [`eval_expr cx obj st = (_,mid)`, `eval_expr cx idx mid = (_,idx_end)`,
          `read_result cx _ idx_end = (_,fin)`] >>
  `?xs. fin.storage_trace = mid.storage_trace ++ xs` by
    (`?xs. idx_end.storage_trace = mid.storage_trace ++ xs` by
       metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
     `?xs. fin.storage_trace = idx_end.storage_trace ++ xs` by
       metis_tac[storage_trace_frame_prefix, storage_trace_frame_read_result] >>
     metis_tac[APPEND_ASSOC]) >>
  `storage_observations_ok cx H mid.storage_trace` by
    (`?xs. u.storage_trace = fin.storage_trace ++ xs` by
       metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
     fs[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `obj` mp_tac) >>
  simp[expr_size_def, MEM_APPEND] >> metis_tac[]
QED
Finalise subscript_expr_result_slot_region_from_pop
