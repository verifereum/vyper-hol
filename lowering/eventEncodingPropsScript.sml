(* Checked argument widening preserves the complete event encoding. The
   signature hash stays the declared event's hash on both sides. *)
Theory eventEncodingProps
Ancestors
  e2eDefs compileEnv vyperEventCompatibility vyperTypeSystem vyperTypeContract
  vyperEvent vyperABI list

Theorem event_compatible_list_rel:
  event_arg_compatible_list ftys atys <=>
  LIST_REL event_arg_compatible ftys atys
Proof
  qid_spec_tac `atys` >> Induct_on `ftys` >>
  Cases_on `atys` >> simp[event_arg_compatible_def]
QED

Theorem log_non_indexed_types_preserve:
  LIST_REL R ftys atys /\ EVERY P ftys /\ EVERY Q atys ==>
  LIST_REL R (log_non_indexed_types flags ftys) (log_non_indexed_types flags atys) /\
  EVERY P (log_non_indexed_types flags ftys) /\
  EVERY Q (log_non_indexed_types flags atys)
Proof
  qid_spec_tac `atys` >> qid_spec_tac `ftys` >> Induct_on `flags`
  >- (Cases_on `ftys` >> Cases_on `atys` >> simp[log_non_indexed_types_def]) >>
  qx_gen_tac `flag` >> qx_gen_tac `ftys` >> qx_gen_tac `atys` >>
  Cases_on `ftys` >> Cases_on `atys` >> Cases_on `flag` >>
  simp[log_non_indexed_types_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem compatible_indexed_event_topics:
  LIST_REL event_arg_compatible ftys atys /\
  LIST_REL (\flag fty. flag ==> event_indexable_type fty) flags ftys ==>
  encode_indexed_event_topics flags ftys vs =
  encode_indexed_event_topics flags atys vs
Proof
  qid_spec_tac `vs` >> qid_spec_tac `atys` >> qid_spec_tac `ftys` >>
  Induct_on `flags`
  >- (Cases_on `ftys` >> Cases_on `atys` >> Cases_on `vs` >>
      simp[encode_indexed_event_topics_def]) >>
  qx_gen_tac `flag` >> qx_gen_tac `ftys` >> qx_gen_tac `atys` >> qx_gen_tac `vs` >>
  Cases_on `ftys` >> Cases_on `atys` >> Cases_on `vs` >> Cases_on `flag` >>
  simp[encode_indexed_event_topics_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  FIRST [drule_all event_arg_compatible_topic >> simp[], simp[]]
QED

Theorem compatible_event_metadata_encoding:
  LIST_REL event_arg_compatible ftys atys /\
  EVERY (well_formed_type tenv) ftys /\ EVERY (well_formed_type tenv) atys /\
  LIST_REL (\flag fty. flag ==> event_indexable_type fty) flags ftys ==>
  encode_vyper_event_metadata tenv logger (hash,ftys,flags) vs =
  encode_vyper_event_metadata tenv logger (hash,atys,flags) vs
Proof
  rpt strip_tac >>
  `encode_indexed_event_topics flags ftys vs =
   encode_indexed_event_topics flags atys vs` by
    (irule compatible_indexed_event_topics >> simp[]) >>
  Cases_on `encode_indexed_event_topics flags ftys vs`
  >- gvs[encode_vyper_event_metadata_def] >>
  `LENGTH flags = LENGTH ftys /\ LENGTH flags = LENGTH vs` by
    fs[encode_indexed_event_topics_characterization] >>
  `LENGTH flags = LENGTH atys` by (imp_res_tac LIST_REL_LENGTH >> simp[]) >>
  `?ftyped. non_indexed_event_args flags ftys vs = SOME ftyped /\
    MAP FST ftyped = log_non_indexed_types flags ftys /\
    MAP SND ftyped = log_non_indexed_values flags vs` by
    (irule non_indexed_event_args_exists >> simp[]) >>
  rename1 `non_indexed_event_args flags ftys vs = SOME ftyped` >>
  `?atyped. non_indexed_event_args flags atys vs = SOME atyped /\
    MAP FST atyped = log_non_indexed_types flags atys /\
    MAP SND atyped = log_non_indexed_values flags vs` by
    (irule non_indexed_event_args_exists >> simp[]) >>
  rename1 `non_indexed_event_args flags atys vs = SOME atyped` >>
  `LIST_REL event_arg_compatible (log_non_indexed_types flags ftys)
      (log_non_indexed_types flags atys) /\
   EVERY (well_formed_type tenv) (log_non_indexed_types flags ftys) /\
   EVERY (well_formed_type tenv) (log_non_indexed_types flags atys)` by
    (irule log_non_indexed_types_preserve >> simp[]) >>
  `event_arg_compatible_list (log_non_indexed_types flags ftys)
      (log_non_indexed_types flags atys)` by simp[event_compatible_list_rel] >>
  `vyper_to_abi_types tenv (log_non_indexed_types flags ftys) =
   vyper_to_abi_types tenv (log_non_indexed_types flags atys)` by
    (irule (cj 2 event_arg_compatible_abi_type) >> simp[]) >>
  `!vals. vyper_to_abi_list tenv (log_non_indexed_types flags ftys) vals =
          vyper_to_abi_list tenv (log_non_indexed_types flags atys) vals` by
    (gen_tac >> irule (cj 2 event_arg_compatible_abi_value) >> simp[]) >>
  simp[encode_vyper_event_metadata_def]
QED
