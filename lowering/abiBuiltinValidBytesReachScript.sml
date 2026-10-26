(* Containing-function execution of the complete noncanonical bytes decoder. *)
Theory abiBuiltinValidBytesReach
Ancestors
  abiBuiltinValidBytes abiBuiltinValidBytesPre abiDecoderBytes abiDecoderContract
  abiBuiltinAllocationState abiBuiltinDecodeSetup abiDecoderReentry abiDecoderLoop
  abiEncoderSequenceReach abiEncoder builtinAbi fragExec instIdxIndep
  valueEncoding compileEnv emitHelperProps venomState venomExecSemantics words list

Theorem lower_abi_decode_valid_bytes:
  lower_abi_decode data (DecBytestring n) min_size max_size
    (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_allocas /\
    actual.vs_alloca_next =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_alloca_next /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all lower_abi_decode_valid_bytes_sequence >> strip_tac >>
  drule abi_builtin_bytes_code >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_BYTES_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin valid bytes reach not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidBytesReach");
