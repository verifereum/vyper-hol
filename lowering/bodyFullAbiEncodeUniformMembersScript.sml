Theory bodyFullAbiEncodeUniformMembers
Ancestors
  exprSimAbiEncodePlanMetadata abiEncoderSourceAggregate abiEncoderOpenInput
  abiDecodeRanges list rich_list option

Theorem abi_encode_uniform_members:
  LENGTH ts = LENGTH infos /\ LENGTH ts = LENGTH cts /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    ((!tv. evaluate_type E (EL i ts) = SOME tv ==>
      is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
      abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
     (!tv v av. evaluate_type E (EL i ts) = SOME tv /\ value_has_type tv v /\
       vyper_to_abi E (EL i ts) v = SOME av ==>
       ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) av /\
         !mem a. val_in_memory tv v a mem ==>
           abi_encoder_open_input ei (EL i cts) rv a (type_memory_size tv) mem)) /\
    abi_sz = abi_member_head_size (EL i cts) /\ dyn = is_dynamic (EL i cts) /\
    (?tv. evaluate_type E (EL i ts) = SOME tv /\ mem_sz = type_memory_size tv)) /\
  LENGTH tvs = LENGTH ts /\ LENGTH vs = LENGTH ts /\ LENGTH avs = LENGTH ts /\
  (!i. i < LENGTH ts ==> evaluate_type E (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    vyper_to_abi E (EL i ts) (EL i vs) = SOME (EL i avs)) ==>
  ?rvs. LENGTH rvs = LENGTH ts /\
    !i ei abi_sz mem_sz dyn. i < LENGTH ts /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type E (EL i ts)) (EL i avs) /\
      !mem a. val_in_memory (EL i tvs) (EL i vs) a mem ==>
        abi_encoder_open_input ei (EL i cts) (EL i rvs) a mem_sz mem
Proof
  strip_tac >>
  `!i. ?rv. !ei abi_sz mem_sz dyn. i < LENGTH ts /\
      EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) (EL i avs) /\
      !mem a. val_in_memory (EL i tvs) (EL i vs) a mem ==>
        abi_encoder_open_input ei (EL i cts) rv a mem_sz mem` by
    (gen_tac >> Cases_on `i < LENGTH ts` >- (
       `?ei abi_sz mem_sz dyn. EL i infos = (ei,abi_sz,mem_sz,dyn)` by
         (Cases_on `EL i infos` >> PairCases_on `r` >> simp[]) >>
       qpat_assum `!i. i < _ ==> _` (qspec_then `i` mp_tac) >>
       (impl_tac >- simp[]) >> strip_tac >>
       qpat_assum `!i ei abi_sz mem_sz dyn. _`
         (qspecl_then [`i`,`ei`,`abi_sz`,`mem_sz`,`dyn`] mp_tac) >>
       (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
       first_x_assum drule >> disch_then drule >> disch_then drule >>
       strip_tac >> qexists `rv` >> simp[]) >> simp[]) >>
  pop_assum (qx_choose_then `f` assume_tac o CONV_RULE SKOLEM_CONV) >>
  qexists `GENLIST f (LENGTH ts)` >> simp[EL_GENLIST]
QED

Theorem abi_encode_uniform_members_map:
  E SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  (!t. MEM t ts ==> IS_SOME (evaluate_type E t) /\
    ?ct.
      (!tv. evaluate_type E t = SOME tv ==>
        is_dynamic ct = is_dynamic (vyper_to_abi_type E t) /\
        abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E t)) /\
      (!tv v av. evaluate_type E t = SOME tv /\ value_has_type tv v /\
        vyper_to_abi E t v = SOME av ==>
        ?rv. enc ct rv = enc (vyper_to_abi_type E t) av /\
          !mem a. val_in_memory tv v a mem ==>
            abi_encoder_open_input (f t) ct rv a (type_memory_size tv) mem)) ==>
  ?cts. LENGTH ts = LENGTH cts /\
    !i. i < LENGTH ts ==>
      ((!tv. evaluate_type E (EL i ts) = SOME tv ==>
        is_dynamic (EL i cts) = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
        abi_member_head_size (EL i cts) = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
       (!tv v av. evaluate_type E (EL i ts) = SOME tv /\ value_has_type tv v /\
         vyper_to_abi E (EL i ts) v = SOME av ==>
         ?rv. enc (EL i cts) rv = enc (vyper_to_abi_type E (EL i ts)) av /\
           !mem a. val_in_memory tv v a mem ==>
             abi_encoder_open_input (f (EL i ts)) (EL i cts) rv a (type_memory_size tv) mem)) /\
      abi_embedded_static_size ce.ce_struct_fields (EL i ts) = abi_member_head_size (EL i cts) /\
      is_abi_dynamic ce.ce_struct_fields (EL i ts) = is_dynamic (EL i cts) /\
      (?tv. evaluate_type E (EL i ts) = SOME tv /\
        type_memory_bytes ce (EL i ts) = type_memory_size tv)
Proof
  strip_tac >>
  `!i. ?ct. i < LENGTH ts ==>
      ((!tv. evaluate_type E (EL i ts) = SOME tv ==>
        is_dynamic ct = is_dynamic (vyper_to_abi_type E (EL i ts)) /\
        abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type E (EL i ts))) /\
       (!tv v av. evaluate_type E (EL i ts) = SOME tv /\ value_has_type tv v /\
         vyper_to_abi E (EL i ts) v = SOME av ==>
         ?rv. enc ct rv = enc (vyper_to_abi_type E (EL i ts)) av /\
           !mem a. val_in_memory tv v a mem ==>
             abi_encoder_open_input (f (EL i ts)) ct rv a (type_memory_size tv) mem)) /\
      abi_embedded_static_size ce.ce_struct_fields (EL i ts) = abi_member_head_size ct /\
      is_abi_dynamic ce.ce_struct_fields (EL i ts) = is_dynamic ct /\
      (?tv. evaluate_type E (EL i ts) = SOME tv /\
        type_memory_bytes ce (EL i ts) = type_memory_size tv)` by
    (gen_tac >> Cases_on `i < LENGTH ts` >- (
      qpat_x_assum `!t. MEM t ts ==> _` (qspec_then `EL i ts` mp_tac) >>
      (impl_tac >- simp[EL_MEM]) >> strip_tac >>
      `?tv. evaluate_type E (EL i ts) = SOME tv` by metis_tac[IS_SOME_EXISTS] >>
      drule_all abi_encode_element_metadata >> strip_tac >>
      qexists `ct` >> simp[] >>
      first_x_assum (qspec_then `tv` mp_tac) >> simp[abi_member_head_size_def]) >> simp[]) >>
  pop_assum (qx_choose_then `g` assume_tac o CONV_RULE SKOLEM_CONV) >>
  qexists `GENLIST g (LENGTH ts)` >> simp[EL_GENLIST]
QED
