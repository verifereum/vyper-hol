Theory lowerDloadNormalJump
Ancestors
  lowerDloadNormalData lowerDloadJumpProducer lowerDloadCoverageInvariant
  lowerDloadSharedState venomState venomInst venomExecSemantics ptrDiscipline
  o1LowerDloadRunnerBoundary o1LowerDloadSourceEntry lowerDloadOwnership
  finite_map list pred_set

Theorem ld_normal_data_jump:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un
    (jump_to lbl s) (jump_to lbl t) astk live keys d A suspended gstk f <=>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un
    s t astk live keys d A suspended gstk f
Proof
  simp[ld_normal_data_def, ld_frame_data_def,
       ld_jump_frame_transport, ld_jump_owned_transport,
       ld_jump_account_transport, ld_shared_state_def,
       jump_to_def, lookup_var_def, allocas_from_def, read_memory_def]
QED

Theorem ld_successful_terminator_branch:
  is_terminator i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  MEM i.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >>
  Cases_on `i.inst_opcode` >>
  gvs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED
