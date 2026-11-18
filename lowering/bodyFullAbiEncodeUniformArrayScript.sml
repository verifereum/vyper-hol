Theory bodyFullAbiEncodeUniformArray
Ancestors
  abiEncoderSourceAggregate abiEncoderSourceTransport abiEncoderOpenInput
  sourceAbiArray vyperABI vyperValue vyperTypeSystem vyperTypeValues vyperTyping valueEncoding valueEncodingDefs
  abiDecodeRanges contractABI list rich_list arithmetic

Theorem abi_encode_uniform_dynarray:
  evaluate_type E ty = SOME tv /\
  (!tv. evaluate_type E ty = SOME tv ==>
    is_dynamic ct = is_dynamic (vyper_to_abi_type E ty) /\
    abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E ty)) /\
  (!tv v av. evaluate_type E ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi E ty v = SOME av ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
      !mem a. val_in_memory tv v a mem ==>
        abi_encoder_open_input ei ct rv a (type_memory_size tv) mem) ==>
  (!atv. evaluate_type E (ArrayT ty (Dynamic n)) = SOME atv ==>
    is_dynamic (Array NONE ct) = is_dynamic (vyper_to_abi_type E (ArrayT ty (Dynamic n))) /\
    abi_member_head_size (Array NONE ct) = abi_member_head_size (vyper_to_abi_type E (ArrayT ty (Dynamic n)))) /\
  (!atv v av. evaluate_type E (ArrayT ty (Dynamic n)) = SOME atv /\ value_has_type atv v /\
    vyper_to_abi E (ArrayT ty (Dynamic n)) v = SOME av ==>
    ?rv. enc (Array NONE ct) rv = enc (vyper_to_abi_type E (ArrayT ty (Dynamic n))) av /\
      !mem a. val_in_memory atv v a mem ==>
        abi_encoder_open_input (AbiDynArray ei (abi_member_head_size ct) (type_memory_size tv) (is_dynamic ct))
          (Array NONE ct) rv a (type_memory_size atv) mem)
Proof
  strip_tac >> conj_tac
  >- simp[vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
  rpt strip_tac >>
  `atv = ArrayTV tv (Dynamic n)` by gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `all_have_type tv vs` >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule vyper_to_abi_same_EL >> strip_tac >>
  `!i. ?rv. i < LENGTH vs ==>
    enc ct rv = enc (vyper_to_abi_type E ty) (EL i avs) /\
    !mem a. val_in_memory tv (EL i vs) a mem ==>
      abi_encoder_open_input ei ct rv a (type_memory_size tv) mem` by
    (gen_tac >> Cases_on `i < LENGTH vs` >- (
      `value_has_type tv (EL i vs)` by gvs[all_have_type_EVERY, EVERY_EL] >>
      simp[] >> qpat_x_assum `!v av. _` irule >> simp[] >>
      qexists `EL i vs` >> simp[]) >> simp[]) >>
  pop_assum (qx_choose_then `f` assume_tac o CONV_RULE SKOLEM_CONV) >>
  qexists `ListV (GENLIST f (LENGTH vs))` >> conj_tac
  >- (`enc (Array NONE ct) (ListV (GENLIST f (LENGTH vs))) =
        enc (Array NONE (vyper_to_abi_type E ty)) (ListV avs)` by
        (irule abi_encoder_dynamic_array_encoding_cong >> simp[EL_GENLIST]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_dynamic_source >>
  simp[value_has_type_def, Once vyper_to_abi_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `!t env av. _`
    (qspecl_then [`ty`,`E`,`ListV avs`] mp_tac) >> simp[] >> strip_tac >>
  irule abiEncoderOpenInputTheory.open_array >> simp[] >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >> fs[type_slot_size_def] >>
  `n <= n * type_slot_size tv` by simp[LE_MULT_LCANCEL] >> decide_tac
QED
