(* Execute the actual word temporary's allocation and MSTORE, including reuse. *)
Theory abiBuiltinEncodeWordStageSequence
Ancestors
  abiBuiltinEncodeWordStageCode abiBuiltinAllocationState abiBuiltinAllocation abiBuiltinEncodeFinishSequence
  abiEncoderWrites abiDecoderReentry abiDecoderContract abiDecoderGuards abiDecoderFrameCompose
  compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics finite_map words list arithmetic

Theorem abi_builtin_encode_word_stage_sequence:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  sb < dimword (:256) /\ staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand buf.buf_operand actual = SOME (n2w sb) /\ mload sb actual = w /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `allocated.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `p` |-> `sb:num`,
    `outsz` |-> `32:num`, `st'` |-> `allocated`] abi_builtin_alloc_buffer_frame) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var st.cs_next_id 32 initial addressed` >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `eval_operand value_op addressed = SOME w` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  `run_inst_seq (emitted_insts st staged) initial = OK (mstore sb w addressed) /\
   inst_extends st staged` by
    (mp_tac (Q.INST [`st1` |-> `allocated`, `st2` |-> `staged`, `s` |-> `initial:venom_state`,
      `s1` |-> `addressed:venom_state`, `s2` |-> `mstore sb w addressed`]
      abi_decode_sequence_chain) >> asm_simp_tac bool_ss []) >>
  `abi_decode_frame sb 32 initial (mstore sb w addressed)` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  qexists_tac `mstore sb w addressed` >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_STAGE_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word staging execution not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordStageSequence");
