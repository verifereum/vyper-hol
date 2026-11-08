(* Source-valued decoder execution installed before registration and body. *)
Theory entryReachBodySourceInstalledDecoder
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySourceRecursiveExecution entryReachBodyFirstEmissionGuarded

Theorem entry_source_registration_decoder_endpoint:
  !ce env ty tv av v ctx fn oid root extent ambient b cap site limit_st
   dst src st last sb cell s body_ce args off cef registered key ut iv body rt z.
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  entry_source_metadata ce env ce.ce_struct_fields ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
  sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  cell+type_memory_size tv < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w cell) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ abi_decoder_code st last /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET ambient /\
  oid NOTIN ambient /\ entry_scratch_ready ambient b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent cell (type_memory_size tv) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  compile_register_positional_args body_ce args off last = (cef,registered) /\
  compile_guarded_body cef F key ut iv body rt registered = ((),z) /\
  fn_has_code last z fn ==>
  ?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    b cap site limit_st st last cell tv v s t
Proof
  rpt gen_tac >> strip_tac >>
  irule entry_source_canonical_window_endpoint >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[registration_guarded_body_empty_phi] >>
  qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`src`,`sb`] >> simp[]
QED
