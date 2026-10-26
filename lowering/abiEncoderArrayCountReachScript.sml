(* The real array count copy reaches its CFG endpoint under enclosing freshness. *)
Theory abiEncoderArrayCountReach
Ancestors
  abiEncoderArrayCountCopy abiEncoderSequenceReach abiDecoderArrayLoopInit abiDecoderArrayHeader
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderGuards
  fragExec instIdxIndep compileEnv emitHelperProps exprLoweringProps emitHelper
  valueEncoding valueEncodingProps venomState venomExecSemantics words list

Theorem abi_encoder_array_count_live:
  abi_decode_array_header dst src opc st = (cnt,st') ==>
  abi_decoder_operand_live st'.cs_next_var cnt
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac abi_decoder_operand_live_emit >> imp_res_tac emitted_insts_emit_void >> gvs[]
QED

Theorem abi_encoder_array_count_reach:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ db < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand cnt actual = SOME (mload sb initial) /\
    mem_word_at db actual.vs_memory = mload sb initial /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_CONJ] >>
  drule_all abi_encoder_array_count_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_COUNT_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder count reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCountReach");
