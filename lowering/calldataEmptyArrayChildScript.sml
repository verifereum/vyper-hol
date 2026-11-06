(* Empty complex children use the offset-free setup, even for dynamic ABI types. *)
Theory calldataEmptyArrayChild
Ancestors
  calldataStaticSetupEndpoint calldataValidMemberEndpoint abiDecoderEmpty
  abiDecoderStaticLoopSetup successfulSequenceEndpoint calldataDynOwned calldataDynStep
  abiDecoderArraySetupInputs abiDecoderReentry abiDecoderExecution instIdxIndep
  compileEnv exprLoweringProps abiDecoderContract safeSequence fragExecMem venomMemDefs
  venomState venomExecSemantics words list arithmetic abiDecoderOffset abiDecoderCoherence
  vyperTyping valueEncoding valueEncodingTyping exprLowering
  calldataSourceMemberFold calldataMemberResourceFrame abiDecoderComplexHead abiDecoderGuard abiEncoder

Theorem calldata_offset_free_array_setup_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    di asz msz st = (ops,ready) /\ ~dec_info_needs_offset di /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas iid = SOME (slot,32) /\ alloca_inv initial /\
  slot < dimword (:256) /\ fn_has_code st ready fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?endpoint.
    ~endpoint.vs_halted /\ endpoint.vs_current_bb = ready.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) endpoint = SOME (n2w j) /\
    eval_operand (FST (SND ops)) endpoint = SOME (n2w (sb+32+j*asz)) /\
    eval_operand (SND (SND ops)) endpoint = SOME (n2w (d+32+j*msz)) /\
    fresh_vars_wrt limit_st endpoint /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op endpoint = eval_operand op initial) /\
    endpoint.vs_memory = initial.vs_memory /\
    endpoint.vs_call_ctx = initial.vs_call_ctx /\
    endpoint.vs_data_section = initial.vs_data_section /\
    endpoint.vs_allocas = initial.vs_allocas /\
    endpoint.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn endpoint) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn endpoint = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn endpoint ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w slot : bytes32) = slot` by simp[] >>
  `mload (w2n (n2w slot : bytes32)) initial = n2w j` by simp[] >>
  `slot+32 <= initial.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  drule_all abi_decode_static_element_setup_shape >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st ready) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (drule calldata_element_setup_opcodes >> simp[EVERY_MEM]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `n2w slot`] >>
     goal_assum (drule_at Any) >> simp[w2n_n2w] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `t` |-> `prepared`, `P` |-> `\s. T`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  simp[eval_op_inst_idx] >> strip_tac >>
  qexists_tac `prepared with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def]
QED

Theorem calldata_empty_dynamic_child_value:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\ value_has_type tv v ==>
  type_memory_bytes ce ty = 0 /\ type_memory_size tv = 0 /\
  val_wf tv v /\ (!d mem. val_in_memory tv v d mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[abi_decoder_empty_dynamic_translation, abi_decoder_coherent_array_iff] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >>
  gvs[value_has_type_def] >>
  rename1 `sparse_has_type _ 0 sparse` >> Cases_on `sparse` >>
  gvs[value_has_type_def, type_memory_bytes_def, type_memory_size_def,
      val_wf_def, val_in_memory_def] >> PairCases_on `h` >> gvs[value_has_type_def]
QED

Theorem calldata_empty_array_child_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) asz (type_memory_size tv) st = (ops,ready) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\ value_has_type tv v /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas iid = SOME (slot,32) /\ alloca_inv initial /\
  alloca_frontier_inv ctx fn site initial /\
  calldata_member_own fn st.cs_next_id last.cs_next_id initial /\
  slot < dimword (:256) /\ fn_has_code st last fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?endpoint.
    eval_operand (FST ops) endpoint = SOME (n2w j) /\
    eval_operand (FST (SND ops)) endpoint = SOME (n2w (sb+32+j*asz)) /\
    eval_operand (SND (SND ops)) endpoint = SOME (n2w (d+32+j*type_memory_size tv)) /\
    endpoint.vs_memory = initial.vs_memory /\
    endpoint.vs_allocas = initial.vs_allocas /\
    endpoint.vs_alloca_next = initial.vs_alloca_next /\
    calldata_member_success ctx fn site limit_st st last
      (d+32+j*type_memory_size tv) (type_memory_size tv) tv v initial endpoint []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `last = ready` by
    (gvs[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
       abi_decode_le_guard_def, comp_return_def]) >> gvs[] >>
  drule_all calldata_empty_dynamic_child_value >> strip_tac >>
  `~dec_info_needs_offset (DecComplex T [])` by
    simp[dec_info_needs_offset_def] >>
  drule_all calldata_offset_free_array_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `calldata_member_resource_frame ctx fn site limit_st st.cs_next_id last.cs_next_id
     st.cs_next_var (d+32+j*type_memory_size tv) (type_memory_size tv)
     initial endpoint []` by
    (irule calldata_member_resource_unchanged >> simp[]) >>
  qexists_tac `endpoint` >>
  fs[calldata_member_success_def, calldata_member_transfers_def]
QED
