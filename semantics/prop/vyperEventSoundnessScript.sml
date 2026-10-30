Theory vyperEventSoundness
Ancestors
  vyperTypeABI vyperEventCompatibility vyperTypeEventLookup vyperTypeEnvExtension
  vyperEvent vyperValue vyperTyping vyperTypeSystem vyperTypeContract vyperABI list

Theorem typed_event_topic_total:
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?topic. encode_event_topic ty v = SOME topic
Proof
  Cases_on `ty` >> simp[encode_event_topic_def, is_event_bytestring_type_def] >>
  Cases_on `b` >> simp[is_event_bytestring_type_def] >>
  TRY (Cases_on `b'` >> simp[is_event_bytestring_type_def]) >>
  rpt strip_tac >> gvs[evaluate_type_def, value_has_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem typed_event_args_total:
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) tys vs /\
  LENGTH flags = LENGTH tys ==>
  (?topics. encode_indexed_event_topics flags tys vs = SOME topics) /\
  (?typed avs. non_indexed_event_args flags tys vs = SOME typed /\
     vyper_to_abi_list tenv (MAP FST typed) (MAP SND typed) = SOME avs)
Proof
  qid_spec_tac `vs` >> qid_spec_tac `flags` >> Induct_on `tys`
  >- (Cases_on `flags` >> Cases_on `vs` >>
      simp[encode_indexed_event_topics_def, non_indexed_event_args_def, vyper_to_abi_def]) >>
  Cases_on `flags` >> Cases_on `vs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all typed_event_topic_total >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  Cases_on `h` >>
  simp[encode_indexed_event_topics_def, non_indexed_event_args_def, vyper_to_abi_def]
QED

Theorem typed_event_metadata_total:
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) tys vs /\
  LENGTH flags = LENGTH tys ==>
  ?ev. encode_vyper_event_metadata tenv logger (hash,tys,flags) vs = SOME ev
Proof
  strip_tac >> drule_all typed_event_args_total >> strip_tac >>
  simp[encode_vyper_event_metadata_def]
QED

Theorem compatible_event_values:
  LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) es fields /\
  EVERY (\((_,ty),_). well_formed_type tenv ty) fields /\
  LIST_REL (\e v. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                            value_has_type tv v) es vs ==>
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    (MAP (SND o FST) fields) vs
Proof
  qid_spec_tac `vs` >> qid_spec_tac `fields` >> Induct_on `es`
  >- (Cases_on `fields` >> Cases_on `vs` >> simp[]) >>
  Cases_on `fields` >> Cases_on `vs` >> simp[] >>
  PairCases_on `h` >> simp[] >> rpt strip_tac >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[cj 1 event_arg_compatible_value_has_type]
QED

Theorem checked_log_encoding_success:
  check_contract dep layouts addr mods = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmt env ret (Log (src,name) es) = SOME env' /\
  ALOOKUP sources target = SOME mods /\
  LIST_REL (\e v. ?tv.
    evaluate_type (type_env_all_modules mods) (expr_type e) = SOME tv /\
    value_has_type tv v) es vs ==>
  ?ev. encode_source_event (type_env_all_modules mods) sources target (src,name) vs = SOME ev
Proof
  rpt strip_tac >> gvs[type_log_inversion] >>
  `art = build_contract_type_artifact dep mods /\ contract_namespaces_ok dep mods` by
    gvs[check_contract_def, AllCaseEqs()] >>
  gvs[] >>
  drule_all checked_artifact_source_event_metadata >>
  disch_then (qspec_then `type_env_all_modules mods` assume_tac) >>
  drule build_contract_event_fields_sound >> strip_tac >>
  `EVERY (\((_,ty),_). well_formed_type (type_env_all_modules mods) ty) fields` by
    (drule_all check_contract_event_fields >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[assignable_type_well_formed]) >>
  drule_all compatible_event_values >> strip_tac >>
  simp[encode_source_event_def] >>
  irule typed_event_metadata_total >> simp[]
QED
