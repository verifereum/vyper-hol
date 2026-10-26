(* Reach the actual encoder entry after constructing its primitive source. *)
Theory abiBuiltinEncodeWordStageReach
Ancestors
  abiBuiltinEncodeWordStageSequence abiBuiltinEncodeWordStageCode abiBuiltinAllocationState
  abiEncoderSequenceReach abiEncoderMemory abiEncoderInput abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec instIdxIndep compileEnv valueEncodingProps
  venomState venomExecSemantics words list

Theorem abi_builtin_encode_word_stage_reach:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  sb < dimword (:256) /\ staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf.buf_operand actual = SOME (n2w sb) /\ mload sb actual = w /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_builtin_encode_staged_word_input:
  is_word_type ty /\ has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ mload sb s = w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb 32 s.vs_memory
Proof
  strip_tac >> drule abi_builtin_encode_word_info >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_encoder_input_copy_iff, abi_encoder_word_window, mem_word_at_eq_mload]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_STAGE_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word staging reach not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordStageReach");
