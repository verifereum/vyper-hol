(* The flat target suffix can observe a storage root, but cannot issue a call. *)
Theory s1PrefixAssignTupleFlatTrace
Ancestors
  list rich_list pair vyperState vyperInterpreter vyperCallOutcomeFrame
  vyperEvalMisc vyperPlaceFrames guardMutationTrace

Definition no_outcome_extension_def[local]:
  no_outcome_extension (s:evaluation_state) t <=>
    ?xs. t.storage_trace = s.storage_trace ++ xs /\
         EVERY (\ob. !rq oc. ob <> StorageOutcome rq oc) xs
End

Theorem no_outcome_extension_same_trace[local]:
  t.storage_trace = s.storage_trace ==> no_outcome_extension s t
Proof
  rw[no_outcome_extension_def] >> qexists `[]` >> simp[]
QED

Theorem no_outcome_extension_root[local]:
  no_outcome_extension s
    (s with storage_trace := s.storage_trace ++ [StorageRoot tr slot tv])
Proof
  simp[no_outcome_extension_def] >> qexists `[StorageRoot tr slot tv]` >> simp[]
QED

Theorem no_outcome_bind[local]:
  state_rel_frame no_outcome_extension f /\
  (!v. state_rel_frame no_outcome_extension (g v)) ==>
  state_rel_frame no_outcome_extension (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >>
  rw[no_outcome_extension_def] >> qexists `xs ++ xs'` >>
  simp[APPEND_ASSOC, EVERY_APPEND]
QED

Theorem no_outcome_unchanged_frame[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) f ==>
  state_rel_frame no_outcome_extension f
Proof
  simp[state_rel_frame_def, no_outcome_extension_same_trace]
QED

Theorem no_outcome_return_raise[local]:
  state_rel_frame no_outcome_extension (vyperState$return v) /\
  state_rel_frame no_outcome_extension (vyperState$raise e)
Proof
  simp[state_rel_frame_def, return_def, raise_def, no_outcome_extension_same_trace]
QED

Theorem lookup_global_no_outcome_frame[local]:
  state_rel_frame no_outcome_extension (lookup_global cx src n)
Proof
  simp[state_rel_frame_def, lookup_global_def, bind_def, ignore_bind_def,
       record_storage_event_def, lift_option_type_def, get_immutables_def,
       get_address_immutables_def, return_def, raise_def] >> gen_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, record_storage_event_def,
           get_immutables_def, get_address_immutables_def,
           lift_option_type_def, return_def, raise_def]) >>
  simp[no_outcome_extension_same_trace, no_outcome_extension_root]
QED

Theorem extend_place_attr_no_outcome[local]:
  state_rel_frame no_outcome_extension (extend_place cx pv (AttrSubscript fld))
Proof
  Cases_on `pv`
  >- simp[extend_place_def, no_outcome_return_raise]
  >- (simp[state_rel_frame_result] >>
      metis_tac[extend_place_PlaceR_state, no_outcome_extension_same_trace]) >>
  simp[extend_place_def, no_outcome_return_raise]
QED

Theorem flat_base_place_no_outcome[local]:
  ((?id. t = NameTarget id) \/ (?ns. t = TopLevelNameTarget ns) \/
   (?ns fld. t = AttributeTarget (TopLevelNameTarget ns) fld)) ==>
  state_rel_frame no_outcome_extension (eval_base_place cx t)
Proof
  strip_tac >> gvs[]
  >- (simp[state_rel_frame_result] >>
      metis_tac[eval_base_place_NameTarget_preserves_state,
                no_outcome_extension_same_trace])
  >- (PairCases_on `ns` >> simp[evaluate_def, lookup_global_no_outcome_frame]) >>
  PairCases_on `ns` >> simp[evaluate_def] >> irule no_outcome_bind >>
  simp[lookup_global_no_outcome_frame, extend_place_attr_no_outcome]
QED

Theorem flat_assign_target_no_outcome[local]:
  ((?id. g = BaseTarget (NameTarget id)) \/
   (?ns. g = BaseTarget (TopLevelNameTarget ns)) \/
   (?ns fld. g = BaseTarget (AttributeTarget (TopLevelNameTarget ns) fld))) ==>
  state_rel_frame no_outcome_extension (assign_tuple_targets cx g v)
Proof
  `!pv. state_rel_frame no_outcome_extension (get_place pv)` by
    (simp[state_rel_frame_result] >> metis_tac[get_place_state, no_outcome_extension_same_trace]) >>
  disch_tac >>
  `?t. g = BaseTarget t /\
       state_rel_frame no_outcome_extension (eval_base_place cx t)` by
    metis_tac[flat_base_place_no_outcome] >>
  qpat_x_assum `g = BaseTarget _` SUBST1_TAC >>
  simp[Once evaluate_def] >> irule no_outcome_bind >>
  simp[no_outcome_unchanged_frame, write_place_trace] >>
  pure_once_rewrite_tac[evaluate_def] >> irule no_outcome_bind >> simp[]
QED

Theorem flat_assign_target_list_no_outcome[local]:
  !gs vs. EVERY (\g. (?id. g = BaseTarget (NameTarget id)) \/
                  (?ns. g = BaseTarget (TopLevelNameTarget ns)) \/
                  (?ns fld. g = BaseTarget (AttributeTarget (TopLevelNameTarget ns) fld))) gs ==>
    state_rel_frame no_outcome_extension (assign_tuple_target_list cx gs vs)
Proof
  Induct >> Cases_on `vs` >>
  simp[evaluate_def, no_outcome_return_raise, ignore_bind_def] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  irule no_outcome_bind >> simp[] >>
  metis_tac[flat_assign_target_no_outcome]
QED

Theorem assign_tuple_flat_no_outcome:
  EVERY (\g. (?id. g = BaseTarget (NameTarget id)) \/
           (?ns. g = BaseTarget (TopLevelNameTarget ns)) \/
           (?ns fld. g = BaseTarget (AttributeTarget (TopLevelNameTarget ns) fld))) gs /\
  assign_tuple_targets cx (TupleTarget gs) v st = (res,ee) ==>
  EVERY (\ob. !rq oc. ob <> StorageOutcome rq oc)
    (DROP (LENGTH st.storage_trace) ee.storage_trace)
Proof
  strip_tac >>
  `state_rel_frame no_outcome_extension (assign_tuple_targets cx (TupleTarget gs) v)`
    suffices_by (strip_tac >> drule_all state_rel_frame_at >>
                 simp[no_outcome_extension_def] >> strip_tac >>
                 simp[DROP_LENGTH_APPEND]) >>
  Cases_on `v` >>
  TRY (qmatch_goalsub_rename_tac `assign_tuple_targets _ _ (ArrayV av)` >>
       Cases_on `av`) >>
  simp[evaluate_def, no_outcome_return_raise] >>
  irule flat_assign_target_list_no_outcome >> first_assum ACCEPT_TAC
QED
