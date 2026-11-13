(* Successful decoder instructions retain every field outside their workspace. *)
Theory abiDecodeMemStaticFrame
Ancestors
  abiDecoderSiteEffect abiDecoderVarSequence
  exprLoweringProps venomExecSemantics venomState venomInst list

Theorem abi_decode_reentry_step_static_frame[local]:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = OK t ==>
  decode_static_frame s t
Proof
  simp_tac bool_ss [abi_decoder_reentry_opcode_def, MEM] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >>
  asm_rewrite_tac [opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    exec_alloca_def, jump_to_def, AllCaseEqs()] >>
  simp[decode_static_frame_def, venom_state_component_equality]
QED

Theorem abi_decode_reentry_sequence_static_frame:
  !code s t.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  decode_static_frame s t
Proof
  Induct >> simp[run_inst_seq_def, decode_static_frame_refl] >>
  rpt gen_tac >> strip_tac >> Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all abi_decode_reentry_step_static_frame >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[decode_static_frame_trans]
QED
