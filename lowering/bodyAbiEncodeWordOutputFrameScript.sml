(* Allocation identity for the concrete singleton-word output fragment. *)
Theory bodyAbiEncodeWordOutputFrame
Ancestors
  bodyAbiEncodeResultMemory bodyAbiEncodeAllocationState abiBuiltinEncodeCode abiEncoderLeaves
  compilerInstructionSuffix abiEncoderProps emitHelperProps exprLoweringProps
  compileEnv fragExec venomInst pred_set list rich_list arithmetic words
  abiEncoder exprLowering emitHelper loweringShapeDefs context
  localPtrsProps exprSimAlloc exprSimOperands abiEncodeWindowTransport
  abiEncoderWindowPhase abiEncoderRegisteredEffect abiEncoderWindowContract finite_map

Theorem abi_encode_word_output_shape[local]:
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) ==>
  cs_extends st final /\
  EVERY (\i. i.inst_opcode = ALLOCA ==>
    i.inst_id = st.cs_next_id /\
    i.inst_operands = [Lit (n2w (32+32*word_size
      (maxlen+(case mid of NONE => 0 | SOME _ => 4))))] /\
    i.inst_outputs = [STRING #"%" (toString st.cs_next_var)])
    (added_insts st final) /\
  (!id. id IN frag_ids st final ==>
    ?i. MEM i (added_insts st final) /\ i.inst_id = id)
Proof
  Cases_on `mid` >>
  simp[lower_abi_encode_phases, abi_builtin_encode_setup_def,
    abi_builtin_encode_method_id_def, abi_builtin_encode_finish_def,
    Once compile_abi_encode_child_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[added_insts_def, state_insts_def, all_blocks_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def,
    frag_ids_def, cs_extends_def, IS_PREFIX_APPEND,
    LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_encode_word_output_alloca[local]:
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ MEM inst (fn_insts func) /\
  inst.inst_id IN frag_ids st final /\ inst.inst_opcode = ALLOCA ==>
  inst.inst_id = st.cs_next_id /\
  inst.inst_operands = [Lit (n2w (32+32*word_size
    (maxlen+(case mid of NONE => 0 | SOME _ => 4))))] /\
  ?q. inst.inst_outputs = [q] /\ not_local_ptr ce scopes q
Proof
  strip_tac >> drule abi_encode_word_output_shape >> strip_tac >>
  `inst.inst_id = st.cs_next_id /\
   inst.inst_operands = [Lit (n2w (32+32*word_size
     (maxlen+(case mid of NONE => 0 | SOME _ => 4))))] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)]` by
    (drule_all added_insts_function_property >> simp[]) >>
  simp[] >> irule local_ptrs_reserved_fresh >> qexists `st` >> simp[]
QED

Theorem abi_encode_word_output_sites:
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st ==>
  window_alloca_sites func (frag_ids st final) = {st.cs_next_id} /\
  ?inst q. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = st.cs_next_id /\
    inst.inst_operands = [Lit (n2w (32+32*word_size
      (maxlen+(case mid of NONE => 0 | SOME _ => 4))))] /\
    inst.inst_outputs = [q] /\ not_local_ptr ce scopes q
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_encode_window_sites >> strip_tac >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st final /\
     inst.inst_opcode = ALLOCA ==>
     inst.inst_id = st.cs_next_id /\
     inst.inst_operands = [Lit (n2w (32+32*word_size
       (maxlen+(case mid of NONE => 0 | SOME _ => 4))))] /\
     ?q. inst.inst_outputs = [q] /\ not_local_ptr ce scopes q` by
    (rpt strip_tac >> drule_all abi_encode_word_output_alloca >> simp[]) >>
  conj_tac >- (fs[window_alloca_sites_def, EXTENSION] >> metis_tac[]) >>
  fs[window_alloca_sites_def] >> metis_tac[]
QED

Theorem abi_encode_word_registered_phase:
  window_phase ctx func st en {id} [(p,n)] s t /\
  FLOOKUP t.vs_allocas id = SOME (p,n) ==>
  window_phase ctx func st en {id} [] s t
Proof
  simp[window_phase_def, abi_encoder_registered_effect_def] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem abi_encode_word_output_state:
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  n = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) /\
  n < dimword (:256) /\
  window_phase ctx func st final (window_alloca_sites func (frag_ids st final))
    [(p,n)] s t /\ window_mem_frame ctx func s t /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory ==>
  stmt_state_rel ctx func ce cx ee t /\
  (!name b sz. local_region ce ee.scopes t name b sz ==>
    p+n <= b \/ b+sz <= p)
Proof
  strip_tac >> drule_all abi_encode_word_output_sites >>
  disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
  `window_phase ctx func st final {inst.inst_id} [] s t` by
    (irule abi_encode_word_registered_phase >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule abi_encode_word_stage_state >>
     qpat_assum `MEM inst _` (irule_at Any) >>
     qpat_assum `window_phase _ _ _ _ _ [] _ _` (irule_at Any) >>
     qexistsl [`q`, `n`, `p`] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `alloca_inv t /\ local_ptrs_rel func ce ee.scopes t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n)` by metis_tac[] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def]
QED
