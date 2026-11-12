Theory abiEncoderSourceFootprint
Ancestors
  abiEncoderSourceProducer abiEncoderSourceAggregate abiEncoderOpenInput
  abiEncoderProps exprSimDefs exprSimProps loweringPosts valueEncoding vyperValue vyperTyping vyperABI
  abiEncoderSourceWindow abiBuiltinAllocation contractABI compileEnv vyperMisc list
  valueEncodingDefs

Theorem abi_encoder_source_footprint_rep:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. source_rep env ty ei ct /\
    enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_open_input ei ct rv sb (val_footprint tv v) mem
Proof
  rpt strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (drule (cj 1 abi_encoder_uniform_source) >> strip_tac >>
      drule_all source_rep_transport >> metis_tac[]) >>
  Cases_on `v` >> gvs[val_footprint_def] >>
  Cases_on `tv` >> gvs[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> gvs[] >>
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()]
  >- (qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
      simp[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
           is_dynamic_def] >> strip_tac >>
      qexistsl [`String`, `BytesV (MAP n2w_o_ORD s)`] >>
      conj_tac
      >- (simp[source_rep_def, vyper_to_abi_type_def] >>
          rpt strip_tac >> qexists_tac `av` >>
          simp[] >> irule abi_encoder_open_string_source >>
          simp[vyper_to_abi_def] >> metis_tac[]) >>
      conj_tac >- simp[enc_def] >>
      irule abiEncoderOpenInputTheory.bytes >>
      gvs[value_has_type_def, val_in_memory_def, has_type_def,
          valid_length_def, n2w_o_ORD_def, combinTheory.o_DEF] >>
      mp_tac (Q.SPEC `STRLEN s` abi_builtin_word_size_capacity) >>
      simp[MAP_EQ_f, n2w_o_ORD_def]) >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  simp[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
       is_dynamic_def] >> strip_tac >>
  qexistsl [`Bytes NONE`, `BytesV l`] >>
  conj_tac
  >- (simp[source_rep_def, vyper_to_abi_type_def] >>
      rpt strip_tac >> qexists_tac `av` >>
      simp[] >> irule abi_encoder_open_bytes_source >>
      simp[vyper_to_abi_def] >> metis_tac[]) >>
  conj_tac >- simp[enc_def] >>
  irule abiEncoderOpenInputTheory.bytes >>
  gvs[value_has_type_def, val_in_memory_def, has_type_def, valid_length_def] >>
  mp_tac (Q.SPEC `LENGTH (l:word8 list)` abi_builtin_word_size_capacity) >> simp[]
QED

Theorem abi_encoder_source_footprint:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_open_input ei ct rv sb (val_footprint tv v) mem
Proof
  metis_tac[abi_encoder_source_footprint_rep]
QED
