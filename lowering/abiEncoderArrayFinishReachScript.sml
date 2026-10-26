(* Parent cursor bookkeeping reaches its real containing-function endpoint. *)
Theory abiEncoderArrayFinishReach
Ancestors
  abiEncoderArrayFinishSequence abiEncoderArrayScalarCode abiEncoderSequenceReach
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderLoop fragExec instIdxIndep
  compileEnv emitHelperProps exprLoweringProps venomState venomExecSemantics words list

Theorem abi_encode_array_finish_reach:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\ fn_has_code st final func /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (old_word+size_word) /\ mload slot actual = old_word+size_word /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame slot 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encode_array_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_FINISH_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array finish reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayFinishReach");
