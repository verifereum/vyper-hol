(* Source conversion inputs for the unchanged owned decoder endpoint. *)
Theory entryReachBodySourceProducer
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySourceMemberEntry entryReachBodyDescendingProducer
  entryReachBodyScalarConversion entryReachBodyDescendingMetadata
  abiDecoderCoherence exprLowering entryReachBodyConversionSupport supportedTypes

Definition entry_source_certified_child_producer_def:
  entry_source_certified_child_producer cert ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st <=>
    !st last dst src sb cell s.
      compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
        (type_to_abi_dec_info sf ce ty) st = ((),last) /\
      abi_decoder_coherent ce env sf ty tv /\
      entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v /\
      mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
        (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
      sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
      cell+type_memory_size tv < dimword (:256) /\
      eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w cell) /\
      abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
      last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
      fn_has_code st last fn /\ abi_decoder_code st last /\ cert last /\
      fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
      oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
      window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET ambient /\
      oid NOTIN ambient /\ entry_scratch_ready ambient b cap s /\ alloca_inv s /\
      abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
      entry_owned_region oid root extent cell (type_memory_size tv) s /\
      ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      ?t. array_child_result ctx fn oid root extent ambient
        (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
        b cap site limit_st st last cell tv v s t
End

Theorem entry_source_certified_child_uint256_sf:
  entry_source_certified_child_producer cert ce env sf
    (BaseT (UintT 256)) tv av v ctx fn oid root extent ambient b cap site limit_st <=>
  entry_source_certified_child_producer cert ce env sf'
    (BaseT (UintT 256)) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_source_certified_child_producer_def,
    entry_source_metadata_def, abi_decoder_coherent_base_iff,
    type_to_abi_dec_info_def]
QED

Theorem entry_source_scalar_metadata:
  entry_abi_leaf ty /\ ty <> BaseT (BytesT (Fixed 0)) /\
  entry_source_metadata ce env sf ty tv di av v ==>
  entry_descending_metadata ce env sf ty tv di av v
Proof
  simp_tac bool_ss [entry_source_metadata_def, entry_descending_metadata_def] >>
  rpt strip_tac >> simp[] >>
  metis_tac[entry_scalar_conversion_typed, entry_scalar_forward_inverse]
QED

Theorem entry_source_scalar_producer_bridge:
  entry_abi_leaf ty /\ ty <> BaseT (BytesT (Fixed 0)) /\
  entry_descending_certified_child_producer cert ce env sf ty tv av v
    ctx fn oid root extent ambient b cap site limit_st ==>
  entry_source_certified_child_producer cert ce env sf ty tv av v
    ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_source_certified_child_producer_def,
    entry_descending_certified_child_producer_def] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[entry_source_scalar_metadata]
QED
