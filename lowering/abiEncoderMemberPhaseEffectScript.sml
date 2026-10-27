(* Rich observations from actual primitive runs, not from weak simulation. *)
Theory abiEncoderMemberPhaseEffect
Ancestors
  abiEncoderMemberPhaseRaw abiEncoderPrimitiveEffect abiEncoderRegisteredEffect
  abiDecoderReentryAddress abiDecoderContract venomState venomExecSemantics
  compileEnv venomInst venomMemDefs words list

Theorem abi_encoder_member_binary_registered:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp[abi_encoder_registered_effect_def, update_var_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_member_load_registered:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`,
    `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp[abi_encoder_registered_effect_def, update_var_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

val _ =
  if List.exists
       (fn name => List.exists (fn parent => parent = name) (Theory.ancestry "-"))
       ["abiScratchMembers", "abiScratchComplex", "abiEncoderMembersPrepare",
        "abiEncoderMembersCorrect", "abiEncoderComplexStatic"]
  then raise Fail "member phase effects import a legacy invariant/execution owner"
  else ();
