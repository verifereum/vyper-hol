Theory externalReturnActualSourceWindow
Ancestors
  externalReturnSourceWindowProbe abiEncoderProps vyperTyping compileEnv
  contractABI valueEncoding loweringPosts vyperABI vyperValue

Theorem return_source_actual_window:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem
Proof
  strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- metis_tac[return_source_window_probe] >>
  Cases_on `v` >> gvs[val_footprint_def, AllCaseEqs()] >>
  Cases_on `ty` >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[Once abi_enc_plan_cases, is_word_type_def,
      vyper_to_abi_type_def, vyper_base_to_abi_type_def, is_dynamic_def]
  >~ [`StringV s`, `AbiBytestring n`]
  >- (qexistsl_tac [`String`, `BytesV (MAP n2w_o_ORD s)`] >>
      conj_tac >- simp[enc_def] >>
      `abi_encoder_window_input (AbiBytestring n) String
         (BytesV (MAP n2w_o_ORD s)) sb
         (val_footprint (BaseTV (StringT n)) (StringV s)) mem` by
        (irule return_string_source_actual_probe >> simp[] >>
         qexists_tac `env` >> simp[evaluate_type_def, vyper_to_abi_def]) >>
      gvs[val_footprint_def]) >>
  rename1 `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) sb mem` >>
  qexistsl_tac [`Bytes NONE`, `BytesV bs`] >>
  conj_tac >- simp[enc_def] >>
  `abi_encoder_window_input (AbiBytestring n) (Bytes NONE) (BytesV bs) sb
     (val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs)) mem` by
    (irule return_bytes_source_actual_probe >> simp[] >>
     qexists_tac `env` >> simp[evaluate_type_def, vyper_to_abi_def]) >>
  gvs[val_footprint_def]
QED
