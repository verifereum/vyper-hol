(* Actual complex compiler boundary: Lit 0w omits the upper-bound guard. *)
Theory entryReachBodyCanonicalComplexConstructors
Ancestors
  entryReachBodyCanonicalMembers entryReachBodyCanonicalProducerBridge
  abiDecoderMemberInfos abiDecoderFixedMemory abiDecoderFixedInputs
  abiCanonicalHeadSize vyperTypeABI abiEncoder compileEnv vyperABI
  words list rich_list arithmetic

Theorem entry_canonical_complex_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [Once compile_abi_decode_to_buf_def, LET_THM]) >>
  irule entry_canonical_members_endpoint >>
  simp[Excl "enc_def"] >> qexistsl_tac [`avs`,`env`] >>
  simp[Excl "enc_def"] >> rpt strip_tac >>
  irule array_child_producer_member >> first_x_assum irule >> simp[]
QED

Theorem entry_canonical_fixed_array_endpoint:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av /\
  (!avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH vs = n /\ abi_decoder_members ce env ce.ce_struct_fields
      (REPLICATE n ty) (REPLICATE n tv) avs vs ==>
    !i. i < n ==> array_child_producer ce env ty tv (EL i avs) (EL i vs)
      ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n))) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) last t /\
    val_in_memory (ArrayTV tv (Fixed n)) v d t.vs_memory
Proof
  strip_tac >> drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) =
    SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))` by
    simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `!i. i < LENGTH (REPLICATE n ty) ==> array_child_producer ce env
    (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv)) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st` by
    (simp[] >> rpt strip_tac >> simp[EL_REPLICATE] >>
     qpat_x_assum `!avs vs. _` drule_all >> simp[]) >>
  gvs[abi_decoder_fixed_array_infos, Once vyper_to_abi_type_def,
      canonical_array_tuple, map_replicate, Excl "enc_def"] >>
  drule_at (Pat `abi_decoder_members _ _ _ _ _ _ _`) entry_canonical_complex_endpoint >>
  simp[map_replicate, SUM_REPLICATE, Excl "enc_def"] >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule abi_decoder_fixed_array_memory >> simp[]
QED
