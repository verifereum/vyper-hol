(* Compiler-endpoint certificates parameterize recursive child execution. *)
Theory entryReachBodyCertifiedProducer
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyConditionalProducer entryReachBodyCanonicalArrayChild

Definition entry_certified_child_producer_def:
  entry_certified_child_producer cert ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st <=>
    !st last dst src sb cell s.
      compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
        (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
      abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
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

Theorem entry_certified_child_unconditional:
  entry_certified_child_producer (\z. T) ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st <=>
  array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_certified_child_producer_def, array_child_producer_def]
QED

Theorem entry_certified_child_conditional:
  entry_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st <=>
  entry_conditional_array_child_producer ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_certified_child_producer_def, entry_conditional_array_child_producer_def]
QED

Theorem entry_certified_child_apply:
  entry_certified_child_producer cert ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
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
Proof
  strip_tac >> fs[entry_certified_child_producer_def] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`dst`, `sb`, `src`] >> simp[]
QED
