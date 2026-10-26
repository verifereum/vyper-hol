(* Execute the actual parent cursor allocation and head-length initialization. *)
Theory abiEncoderComplexPrefix
Ancestors
  abiEncoderComplexCode abiDecoderIndexInit abiDecoderReentryAllocation abiDecoderAllocation
  abiDecoderReentry abiDecoderArrayHeader abiDecoderGuards abiDecoderContract abiDecoderFrame
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomExecSemantics venomMemProps venomState venomInst finite_map words list rich_list arithmetic

Theorem abi_encoder_complex_prefix_trace:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') ==>
  ?buf allocation_st.
    compile_alloc_buffer 32 st = (buf,allocation_st) /\ dyn_ptr = buf.buf_operand /\
    emit_void MSTORE [buf.buf_operand;
      Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))] allocation_st = ((),st')
Proof
  strip_tac >> Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocation_st)` >>
  qexistsl_tac [`buf`, `allocation_st`] >>
  gvs[abi_encode_complex_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_void_def, fresh_id_def, emit_def]
QED

Theorem abi_encoder_complex_prefix_shape:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') ==>
  dyn_ptr = Var (STRING #"%" (toString st.cs_next_var)) /\
  st'.cs_next_var = st.cs_next_var+1 /\ st'.cs_next_id = st.cs_next_id+2 /\
  st'.cs_current_bb = st.cs_current_bb /\ st'.cs_blocks = st.cs_blocks /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_encoder_complex_prefix_sequence:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    b <= slot /\ slot+32 <= b+cap /\
    abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    abi_decode_frame slot 32 initial actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule abi_encoder_complex_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `allocation_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_alloc_buffer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) initial = OK allocated` >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `p < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))) allocated =
    SOME (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts allocation_st st') allocated =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_store_sequence >> simp[w2n_n2w]) >>
  `inst_extends st allocation_st /\ inst_extends allocation_st st'` by
    (conj_tac >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  `abi_decode_frame p 32 allocated
    (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    irule abi_decode_mstore_frame >>
  qexistsl_tac [`mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated`, `p`] >>
  gvs[fresh_vars_wrt_mstore, eval_operand_mstore, abi_decode_frame_def, mload_mstore_same,
    mstore_def, write_memory_with_expansion_def] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex prefix not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexPrefix");
