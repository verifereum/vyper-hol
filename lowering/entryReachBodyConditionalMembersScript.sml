(* Installed-exit certificates propagated through heterogeneous member tails. *)
Theory entryReachBodyConditionalMembers
Ancestors
  valueEncodingDefs entryReachBodyCanonicalLocalMembers entryReachBodyCertifiedProducer
  entryReachBodyConditionalProducer calldataRecursiveProducers
  entryReachBodyCanonicalMembers abiDecoderMembers abiDecoderCoherence
  abiEncoderRegisteredEffect abiEncoderWindowContract venomExecSemantics

Theorem entry_conditional_local_members_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_conditional_array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0 st = ((),last) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
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
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. z.cs_current_insts = [] ==> !bb.
    lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0`] entry_certified_local_members_endpoint) >>
  simp[entry_certified_child_conditional, Excl "enc_def"] >>
  (impl_tac >- (rpt strip_tac >>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ elems ao vo a = ((),z)`
      (mp_then (Pos hd) mp_tac calldata_member_tail_empty_exit_phi) >>
    disch_then (qspec_then `fn` mp_tac) >> simp[])) >> simp[]
QED

Theorem entry_conditional_local_complex_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_conditional_array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
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
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. z.cs_current_insts = [] ==> !bb.
    lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0`] entry_certified_local_complex_endpoint) >>
  simp[entry_certified_child_conditional, Excl "enc_def"] >>
  (impl_tac >- (rpt strip_tac >>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ elems ao vo a = ((),z)`
      (mp_then (Pos hd) mp_tac calldata_member_tail_empty_exit_phi) >>
    disch_then (qspec_then `fn` mp_tac) >> simp[])) >> simp[]
QED

Theorem entry_conditional_local_fixed_array_endpoint:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av /\
  (!avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH vs = n /\ abi_decoder_members ce env ce.ce_struct_fields
      (REPLICATE n ty) (REPLICATE n tv) avs vs ==>
    !i. i < n ==> entry_conditional_array_child_producer ce env ty tv (EL i avs) (EL i vs)
      ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n))) st = ((),last) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
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
    val_in_memory (ArrayTV tv (Fixed n)) v d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,type_memory_bytes ce (ArrayT ty (Fixed n)))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. z.cs_current_insts = [] ==> !bb.
    lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0`] entry_certified_local_fixed_array_endpoint) >>
  simp[entry_certified_child_conditional, Excl "enc_def"] >>
  (impl_tac >- (rpt strip_tac >>
    qpat_assum `compile_abi_decode_complex_elems _ _ _ _ elems ao vo a = ((),z)`
      (mp_then (Pos hd) mp_tac calldata_member_tail_empty_exit_phi) >>
    disch_then (qspec_then `fn` mp_tac) >> simp[])) >> simp[]
QED
