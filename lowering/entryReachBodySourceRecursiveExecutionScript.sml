(* Source-valued recursive execution with an installed no-PHI certificate. *)
Theory entryReachBodySourceRecursiveExecution
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySourceLeafArrayClosure entryReachBodySourceAggregateClosure
  entryReachBodySourceProducer abiDecoderCoherence list

Theorem source_certified_producer_induction[local]:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf ty tv /\
  !av v ctx fn oid root extent ambient b cap site limit_st.
    entry_source_certified_child_producer
      (\z. z.cs_current_insts = [] ==> !bb.
        lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
      ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_base_iff] >>
      rpt gen_tac >> irule entry_source_base_producer >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_flag_iff] >>
      rpt gen_tac >> irule entry_source_flag_producer)
  >- (rpt gen_tac >> strip_tac >>
      conj_asm1_tac >- simp[abi_decoder_coherent_array_iff] >>
      rpt gen_tac >> Cases_on `bound`
      >- (irule entry_source_fixed_array_producer >> simp[])
      >> irule entry_source_dynamic_producer >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      fs[LIST_REL_EL_EQN] >>
      conj_asm1_tac
      >- simp[abi_decoder_coherent_tuple_iff, LIST_REL_EL_EQN] >>
      rpt gen_tac >> irule entry_source_tuple_producer >> simp[])
  >> rpt gen_tac >> strip_tac >> fs[LIST_REL_EL_EQN] >>
  conj_asm1_tac
  >- (simp[abi_decoder_coherent_struct_iff] >>
      qexists_tac `tvs` >> simp[LIST_REL_EL_EQN]) >>
  rpt gen_tac >> irule entry_source_struct_producer >> simp[]
QED

Theorem entry_source_certified_producer_exists:
  abi_decoder_coherent ce env sf ty tv ==>
  entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  metis_tac[source_certified_producer_induction]
QED

(* Direct consumer boundary: source conversion replaces aggregate ABI typing;
   installation, scratch ownership and the no-PHI certificate remain explicit. *)
Theorem entry_source_canonical_window_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
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
  fn_has_code st last fn /\ abi_decoder_code st last /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
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
  strip_tac >> drule entry_source_certified_producer_exists >>
  simp_tac bool_ss [entry_source_certified_child_producer_def] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`av`,`dst`,`sb`,`src`] >> simp[]
QED
