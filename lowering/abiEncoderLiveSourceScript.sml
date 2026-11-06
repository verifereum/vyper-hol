Theory abiEncoderLiveSource
Ancestors
  externalReturnWindowResources abiEncoderWindowSource loweringPosts
  abiEncoderProps compileEnv vyperABI contractABI abiEncoderWindow abiEncoderInput

Theorem abi_plan_bytes_inversion[local]:
  abi_enc_plan env (BaseT (BytesT (Dynamic n))) ei ==>
  ei = AbiBytestring n
Proof
  simp[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_plan_string_inversion[local]:
  abi_enc_plan env (BaseT (StringT n)) ei ==> ei = AbiBytestring n
Proof
  simp[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
       vyper_base_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_source_non_nominal_forms[local]:
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  val_footprint tv v <> type_memory_size tv ==>
  (?n bs. ty = BaseT (BytesT (Dynamic n)) /\
          tv = BaseTV (BytesT (Dynamic n)) /\ v = vyperValue$BytesV bs) \/
  (?n str. ty = BaseT (StringT n) /\
           tv = BaseTV (StringT n) /\ v = StringV str)
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rpt strip_tac >> Cases_on `ty` >>
  gvs[vyperValueTheory.evaluate_type_def,
      vyperTypingTheory.value_has_type_def, AllCaseEqs()]
QED

Theorem abi_encoder_live_source_window:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v p mem ==>
  ?at rv. abi_encoder_window_input ei at rv p (val_footprint tv v) mem /\
    enc at rv = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env ty
Proof
  strip_tac >> Cases_on `val_footprint tv v = type_memory_size tv`
  >- (gvs[] >> irule return_plan_nominal_source_window >> metis_tac[]) >>
  drule_all (cj 1 vyperABIValidTheory.vyper_to_abi_enc_le_size_bound) >>
  strip_tac >>
  drule_all abi_source_non_nominal_forms >> strip_tac >>
  gvs[]
  >~ [`abi_enc_plan env (BaseT (BytesT (Dynamic n))) ei`]
  >- (drule abi_plan_bytes_inversion >> strip_tac >> gvs[] >>
      qexistsl_tac [`Bytes NONE`, `contractABI$BytesV bs`] >>
      simp[val_footprint_def, enc_def] >>
      irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
               abi_encoder_window_bytes_source) >>
      qexistsl_tac [`env`, `BaseTV (BytesT (Dynamic n))`,
                    `vyperValue$BytesV bs`] >>
      simp[vyper_to_abi_def]) >>
  drule abi_plan_string_inversion >> strip_tac >> gvs[] >>
  qexistsl_tac [`String`, `contractABI$BytesV (MAP n2w_o_ORD str)`] >>
  simp[val_footprint_def, enc_def] >>
  `vyper_to_abi env (BaseT (StringT n)) (StringV str) =
     SOME (contractABI$BytesV (MAP n2w_o_ORD str))` by
    simp[vyper_to_abi_def] >>
  drule_all abi_encoder_window_string_source >> simp[]
QED

Theorem abi_encoder_window_singleton:
  abi_encoder_window_input ei at rv p cap mem /\ cap <= mem_sz ==>
  abi_encoder_window_input
    (AbiComplex [(ei,abi_member_head_size at,mem_sz,is_dynamic at)])
    (Tuple [at]) (ListV [rv]) p cap mem
Proof
  strip_tac >> simp[abi_encoder_window_complex_iff,
    abi_encoder_tuple_type_def, abi_encoder_member_span_def] >>
  qexists_tac `cap` >> simp[]
QED
