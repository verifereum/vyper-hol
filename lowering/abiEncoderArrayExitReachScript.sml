(* Actual static and dynamic array exits return their lengths at the real CFG endpoint. *)
Theory abiEncoderArrayExitReach
Ancestors
  abiEncoderArrayExitSequence abiEncoderArrayScalarCode abiEncoderPrefixReach
  abiBuiltinPrefix abiDecoderReentryAddress abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec compileEnv venomState words list

Theorem abi_encode_array_static_exit_reach:
  abi_encode_array_static_exit src asz st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+cnt*asz)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
  drule_all abi_encoder_prefix_reach >> simp[]
QED

Theorem abi_encode_array_dynamic_exit_reach:
  abi_encode_array_dynamic_exit src dyn_ptr st = (out,final) /\ fn_has_code st final func /\
  eval_operand src initial = SOME src_word /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ mload slot initial = n2w offset /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w (32+offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
  drule_all abi_encoder_prefix_reach >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_EXIT_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array exit reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayExitReach");
