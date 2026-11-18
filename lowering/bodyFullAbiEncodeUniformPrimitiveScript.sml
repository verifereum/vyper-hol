Theory bodyFullAbiEncodeUniformPrimitive
Ancestors
  exprSimAbiEncodePlanMetadata exprSimAbiEncodePlanDomain abiEncoderSourceWindow entryDecodePlanProps
  vyperABI vyperTypeSystem compileEnv
  abiEncoderOpenInput abiEncoderStaticRepresentative abiEncoderInput abiDecodeRanges valueEncodingProps exprLowering

Theorem abi_encode_uniform_static_copy:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv /\ ~is_abi_dynamic ce.ce_struct_fields ty ==>
  ?ct.
    (!tv. evaluate_type E ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!tv v av. evaluate_type E ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E ty v = SOME av ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (AbiCopy (type_memory_bytes ce ty)) ct rv a
            (type_memory_size tv) mem)
Proof
  strip_tac >> drule_all abi_encode_element_metadata >> strip_tac >> gvs[] >>
  drule_all abi_encoder_static_source_alignment >> strip_tac >>
  drule abi_encoder_uniform_aligned_representative >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  qexists `ct` >> conj_tac
  >- (rpt strip_tac >> gvs[abi_member_head_size_def] >>
      metis_tac[static_length_memory_size]) >>
  rpt strip_tac >> gvs[] >>
  `LENGTH (enc (vyper_to_abi_type E ty) av) = type_memory_size tv` by
    metis_tac[vyper_to_abi_static_enc_length] >>
  first_x_assum drule >> strip_tac >> qexists `av'` >> simp[] >>
  rpt strip_tac >> irule abiEncoderOpenInputTheory.copy >> simp[] >>
  metis_tac[val_in_memory_static_abi]
QED

Theorem abi_encode_uniform_primitive:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv /\
  ((?b. ty = BaseT b) \/ (?k. ty = FlagT k) \/ ty = NoneT) ==>
  ?ct.
    (!tv. evaluate_type E ty = SOME tv ==>
      is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
      abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
    (!tv v av. evaluate_type E ty = SOME tv /\ value_has_type tv v /\
      vyper_to_abi E ty v = SOME av ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
        !mem a. val_in_memory tv v a mem ==>
          abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv a
            (type_memory_size tv) mem)
Proof
  strip_tac
  >~ [`BaseT b`] >- (
    Cases_on `b` >> simp[type_to_abi_enc_info_def]
    >~ [`BytesT bd`] >- (
      Cases_on `bd` >> simp[type_to_abi_enc_info_def]
      >- (`~is_abi_dynamic ce.ce_struct_fields ty` by gvs[is_abi_dynamic_def] >>
          drule_all abi_encode_uniform_static_copy >> simp[]) >>
      qexists `Bytes NONE` >> simp[vyper_to_abi_type_def] >>
      rpt strip_tac >> qexists `av` >> simp[] >> rpt strip_tac >>
      irule abi_encoder_open_bytes_source >> gvs[vyper_to_abi_def] >>
      qexistsl [`E`, `v`] >> simp[])
    >~ [`StringT n`] >- (
      qexists `String` >> simp[vyper_to_abi_type_def] >>
      rpt strip_tac >> qexists `av` >> simp[] >> rpt strip_tac >>
      irule abi_encoder_open_string_source >> gvs[vyper_to_abi_def] >>
      qexistsl [`E`, `v`] >> simp[]) >>
    `~is_abi_dynamic ce.ce_struct_fields ty` by gvs[is_abi_dynamic_def] >>
    drule_all abi_encode_uniform_static_copy >> simp[])
  >~ [`FlagT k`] >- (
    `~is_abi_dynamic ce.ce_struct_fields ty` by gvs[is_abi_dynamic_def] >>
    drule_all abi_encode_uniform_static_copy >> simp[type_to_abi_enc_info_def]) >>
  qexists `Tuple []` >> simp[vyper_to_abi_type_def] >> rpt strip_tac >>
  gvs[vyper_to_abi_def, AllCaseEqs()] >> qexists `ListV []` >>
  simp[abi_encode_none_open_input]
QED
