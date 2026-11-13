(* Uniform dynamic-array construction without a child plan premise. *)
Theory abiEncoderUniformArrayConstructor
Ancestors
  abiEncoderUniformStaticSource abiEncoderUniformSourceMembers
  abiEncoderUniformSourceEncoding
  abiEncoderSourceProducer abiEncoderSourcePrimitive abiEncoderSourceTransport
  abiEncoderSourceAggregate abiEncoderSourceWindow abiEncoderProps abiCallerTupleLayout
  vyperABI contractABI abiDecodeRanges abiEncoderInput list rich_list
  valueEncodingProofs vyperValueOperation abiEncoderOpenInput vyperValue
  valueEncoding vyperTyping

Theorem abi_encoder_uniform_dynarray:
  evaluate_type env ty = SOME tv /\
  (!u. evaluate_type env ty = SOME u ==>
    is_dynamic ct = is_dynamic (vyper_to_abi_type env ty) /\
    abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type env ty)) /\
  (!u v av sb mem0.
    evaluate_type env ty = SOME u /\ value_has_type u v /\
    vyper_to_abi env ty v = SOME av /\ val_in_memory u v sb mem0 ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
      !mem. val_in_memory u v sb mem ==>
        abi_encoder_open_input ei ct rv sb (type_memory_size u) mem) ==>
  (!u. evaluate_type env (ArrayT ty (Dynamic n)) = SOME u ==>
    is_dynamic (Array NONE ct) = is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic n))) /\
    abi_member_head_size (Array NONE ct) =
      abi_member_head_size (vyper_to_abi_type env (ArrayT ty (Dynamic n)))) /\
  (!u v av sb mem0.
    evaluate_type env (ArrayT ty (Dynamic n)) = SOME u /\ value_has_type u v /\
    vyper_to_abi env (ArrayT ty (Dynamic n)) v = SOME av /\
    val_in_memory u v sb mem0 ==>
    ?rv. enc (Array NONE ct) rv = enc (vyper_to_abi_type env (ArrayT ty (Dynamic n))) av /\
      !mem. val_in_memory u v sb mem ==>
        abi_encoder_open_input
          (AbiDynArray ei (abi_member_head_size (vyper_to_abi_type env ty))
            (type_memory_size tv) (is_dynamic (vyper_to_abi_type env ty)))
          (Array NONE ct) rv sb (type_memory_size u) mem)
Proof
  strip_tac >>
  `source_rep env ty ei ct` by (simp[source_rep_def] >> metis_tac[]) >>
  drule_all source_rep_metadata >> strip_tac >>
  simp[vyper_to_abi_type_def, is_dynamic_def, abi_member_head_size_def] >>
  rpt strip_tac >>
  `u = ArrayTV tv (Dynamic n)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV arr` >> Cases_on `arr` >> gvs[value_has_type_def] >>
  rename1 `val_in_memory _ (ArrayV (DynArrayV vs)) _ _` >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_dynamic_source >>
  simp[value_has_type_def, Once vyper_to_abi_def] >> strip_tac >>
  qpat_x_assum `!t env' av'. _`
    (qspecl_then [`ty`, `env`, `av`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `!i. i < LENGTH vs ==> ?rv.
    enc ct rv = enc (vyper_to_abi_type env ty) (EL i avs) /\
    !mem. val_in_memory tv (EL i vs) (sb+32+i*type_memory_size tv) mem ==>
      abi_encoder_open_input ei ct rv (sb+32+i*type_memory_size tv)
        (type_memory_size tv) mem` by
    (rpt strip_tac >> first_assum irule >> simp[] >>
     qexists_tac `mem0` >> simp[arithmeticTheory.ADD_ASSOC]) >>
  qpat_x_assum `!i. _ ==> ?rv. _` mp_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_IMP_THM)))) >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV SKOLEM_THM)) >>
  disch_then (qx_choose_then `f` assume_tac) >>
  qexists_tac `ListV (GENLIST f (LENGTH vs))` >> conj_tac
  >- (`enc (Array NONE ct) (ListV (GENLIST f (LENGTH vs))) =
       enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
        (irule abi_encoder_dynamic_array_encoding_cong >> simp[]) >>
      gvs[Once enc_def]) >>
  rpt strip_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) abi_encoder_dynamic_source >>
  simp[value_has_type_def, Once vyper_to_abi_def] >> strip_tac >>
  qpat_x_assum `!t env' av'. _`
    (qspecl_then [`ty`, `env`, `ListV avs`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  irule abiEncoderOpenInputTheory.open_array >> simp[abi_member_head_size_def] >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >> fs[type_slot_size_def] >>
  `n <= n * type_slot_size tv` by (simp[arithmeticTheory.LE_MULT_LCANCEL]) >> decide_tac
QED
