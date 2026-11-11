(* TOP-LEVEL: source event metadata combines the proved indexed topics with
   native ABI field encodings. APIs: abi_field_event_metadata_encoding,
   empty_event_metadata_encoding.
   Helper: log_non_indexed_values_select. *)
Theory abiLogSourceEncoding
Ancestors
  loweringStateRelDefs abiFieldEncodingsList abiFieldEncodingDefs eventLogSplitProps e2eDefs sourceAbiTypingLists
  compileEnv vyperEvent vyperABI contractABI list words

Theorem log_non_indexed_values_select:
  !flags values. log_non_indexed_values flags values = select_log_args F flags values
Proof
  Induct_on `flags` >- (Cases >> simp[log_non_indexed_values_def, select_log_args_def]) >>
  MAP_EVERY qx_gen_tac [`flag`, `values`] >> Cases_on `values` >> Cases_on `flag` >>
  simp[log_non_indexed_values_def, select_log_args_def]
QED

Theorem abi_field_event_metadata_encoding:
  !tenv sfields cenv flags tys values tvs avs rows logger sig_hash topics.
    encode_indexed_event_topics flags tys values = SOME topics /\
    abi_field_encodings tenv sfields cenv (log_non_indexed_types flags tys)
      tvs (select_log_args F flags values) avs rows ==>
    encode_vyper_event_metadata tenv logger (sig_hash,tys,flags) values =
      SOME <|logger := logger; topics := n2w sig_hash::topics;
        data := enc (Tuple (MAP (vyper_to_abi_type tenv) (log_non_indexed_types flags tys))) (ListV avs)|>
Proof
  rpt gen_tac >> strip_tac >> drule abi_field_encodings_properties >> strip_tac >>
  `LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH values` by
    fs[encode_indexed_event_topics_characterization] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  asm_simp_tac (srw_ss()) [encode_vyper_event_metadata_def, log_non_indexed_values_select, source_abi_types_map]
QED

Theorem empty_event_metadata_encoding:
  !tenv logger sig_hash flags tys values topics.
    encode_indexed_event_topics flags tys values = SOME topics /\ log_non_indexed_types flags tys = [] ==>
    encode_vyper_event_metadata tenv logger (sig_hash,tys,flags) values =
      SOME <|logger := logger; topics := n2w sig_hash::topics; data := []|>
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH values` by fs[encode_indexed_event_topics_characterization] >>
  drule_all_then (qx_choose_then `typed_values` strip_assume_tac) non_indexed_event_args_exists >>
  `typed_values = []` by
    (qpat_x_assum `MAP FST typed_values = _` mp_tac >> asm_simp_tac (srw_ss()) []) >>
  gvs[encode_vyper_event_metadata_def, Once vyper_to_abi_def] >> EVAL_TAC
QED
