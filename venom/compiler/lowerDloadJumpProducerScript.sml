Theory lowerDloadJumpProducer
Ancestors
  lowerDloadPairedBoundary lowerDloadOwnership lowerDloadFrameCertificate
  lowerDloadAllocation ptrDiscipline venomExecSemantics venomState venomInst
  finite_map list pred_set

Theorem ld_jump_backward:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?lbl. t' = jump_to lbl t /\
    step_inst fuelS CS i s = OK (jump_to lbl s)
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Control-only updates do not require initially equal block positions. *)
Theorem ld_jump_owned_transport:
  ld_owned_vars V E AG BH tn un (jump_to lbl s) (jump_to lbl t) <=>
  ld_owned_vars V E AG BH tn un s t
Proof
  simp[ld_owned_vars_def, jump_to_def, lookup_var_def]
QED

Theorem ld_jump_frame_transport:
  ld_frame_embedding E L H (jump_to lbl s) (jump_to lbl t) <=>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_embedding_def, jump_to_def]
QED

Theorem ld_jump_account_transport:
  ld_alloc_account keys d A (jump_to lbl s) (jump_to lbl t) <=>
  ld_alloc_account keys d A s t
Proof
  simp[ld_alloc_account_def, jump_to_def]
QED

Theorem ld_jump_data_projections:
  (jump_to lbl s).vs_memory = s.vs_memory /\
  (jump_to lbl s).vs_allocas = s.vs_allocas /\
  (jump_to lbl s).vs_alloca_next = s.vs_alloca_next /\
  (jump_to lbl s).vs_vars = s.vs_vars /\
  (jump_to lbl s).vs_params = s.vs_params /\
  lookup_var v (jump_to lbl s) = lookup_var v s /\
  eval_operand op (jump_to lbl s) = eval_operand op s
Proof
  Cases_on `op` >> simp[jump_to_def, lookup_var_def, eval_operand_def]
QED
