Theory externalReturnChosenWindow
Ancestors
  externalReturnActualSourceWindow externalReturnSemanticProbe externalReturnSourceWindowProbe
  abiEncoderSourceInvoke abiEncoderProps vyperLoweringCorrect
  vyperTyping vyperABI vyperValue contractABI valueEncoding loweringPosts
  compileEnv abiEncoderInput abiDecodeRanges exprSimProps words list

Theorem return_plan_admissible:
  abi_enc_plan env ty ei ==> abi_encoder_admissible ei
Proof
  metis_tac[abi_enc_plan_admissible]
QED

Theorem return_wrapped_full_window:
  abi_enc_plan env (TupleT [ret]) ei /\
  evaluate_type env ret = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ret v = SOME av /\ val_in_memory tv v sb mem ==>
  ?ct rv. enc ct rv = enc (Tuple [vyper_to_abi_type env ret]) (ListV [av]) /\
    abi_encoder_window_input ei ct rv sb (type_memory_size tv) mem
Proof
  strip_tac >>
  `type_slot_size tv <= dimword (:256)` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed,
              vyperTypingTheory.well_formed_type_value_slot_size] >>
  `evaluate_type env (TupleT [ret]) = SOME (TupleTV [tv])` by
    simp[evaluate_type_def, type_slot_size_def] >>
  `value_has_type (TupleTV [tv]) (ArrayV (TupleV [v]))` by
    simp[value_has_type_def] >>
  `vyper_to_abi env (TupleT [ret]) (ArrayV (TupleV [v])) = SOME (ListV [av])` by
    simp[vyper_to_abi_def] >>
  `val_in_memory (TupleTV [tv]) (ArrayV (TupleV [v])) sb mem` by
    simp[singleton_tuple_memory] >>
  drule_all return_source_window_probe >>
  simp[singleton_tuple_memory_size, vyper_to_abi_type_def]
QED

Theorem return_chosen_window:
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) ei /\
  evaluate_type (type_env tops) ret = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (type_env tops) ret v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem /\
    return_bytes tops ret v (enc ct rv)
Proof
  strip_tac >>
  Cases_on `needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)`
  >- (gvs[] >>
      `return_bytes tops ret v
         (enc (Tuple [vyper_to_abi_type (type_env tops) ret]) (ListV [av]))` by
        (mp_tac chosen_return_abi_bytes >>
         disch_then (qspecl_then [`tops`, `ret`, `v`, `ListV [av]`] mp_tac) >>
         simp[vyper_to_abi_def, vyper_to_abi_type_def]) >>
      Cases_on `val_footprint tv v = type_memory_size tv`
      >- (drule_all return_wrapped_full_window >> metis_tac[]) >>
      Cases_on `v` >> gvs[val_footprint_def, AllCaseEqs()] >>
      Cases_on `ret` >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
      gvs[Once abi_enc_plan_cases, is_word_type_def,
          vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
      gvs[Once (cj 2 abi_enc_plan_cases)] >>
      gvs[Once (cj 2 abi_enc_plan_cases)] >>
      gvs[Once abi_enc_plan_cases, is_word_type_def,
          vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
      gvs[evaluate_type_def]
      >~ [`StringV s`, `AbiBytestring n`]
      >- (qexistsl_tac [`Tuple [String]`, `ListV [BytesV (MAP n2w_o_ORD s)]`] >>
          reverse conj_tac >- simp[enc_def] >>
          `abi_encoder_window_input (AbiBytestring n) String
             (BytesV (MAP n2w_o_ORD s)) sb
             (val_footprint (BaseTV (StringT n)) (StringV s)) mem` by
            (irule return_string_source_actual_probe >> simp[] >>
             qexists_tac `type_env tops` >> simp[evaluate_type_def, vyper_to_abi_def]) >>
          drule return_singleton_window >>
          disch_then (qspec_then `type_memory_size (BaseTV (StringT n))` mp_tac) >>
          gvs[val_footprint_def, value_has_type_def, type_memory_size_def,
              type_slot_size_def, abi_member_head_size_def, is_dynamic_def] >>
          impl_tac >- (qspec_then `n` mp_tac le_word_size_mul >> decide_tac) >> simp[]) >>
      rename1 `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) sb mem` >>
      qexistsl_tac [`Tuple [Bytes NONE]`, `ListV [BytesV bs]`] >>
      reverse conj_tac >- simp[enc_def] >>
      `abi_encoder_window_input (AbiBytestring n) (Bytes NONE) (BytesV bs) sb
         (val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs)) mem` by
        (irule return_bytes_source_actual_probe >> simp[] >>
         qexists_tac `type_env tops` >> simp[evaluate_type_def, vyper_to_abi_def]) >>
      drule return_singleton_window >>
      disch_then (qspec_then `type_memory_size (BaseTV (BytesT (Dynamic n)))` mp_tac) >>
      gvs[val_footprint_def, value_has_type_def, type_memory_size_def,
          type_slot_size_def, abi_member_head_size_def, is_dynamic_def] >>
      impl_tac >- (qspec_then `n` mp_tac le_word_size_mul >> decide_tac) >> simp[]) >>
  gvs[] >> drule_all return_source_actual_window >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >>
  mp_tac chosen_return_abi_bytes >>
  disch_then (qspecl_then [`tops`, `ret`, `v`, `av`] mp_tac) >> simp[]
QED
