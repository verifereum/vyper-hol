Theory lowerDloadStorageWrite
Ancestors
  lowerDloadSharedState lowerDloadMaskedStorage
  venomExecSemantics venomState venomInst ptrDiscipline list words pred_set

Theorem ld_storage_write_backward:
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [a;v] /\
  s.vs_call_ctx = t.vs_call_ctx /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  eval_operand v s = SOME x /\ eval_operand v t = SOME y /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    (i.inst_opcode = SSTORE ==> s' = sstore key x s /\ t' = sstore key y t) /\
    (i.inst_opcode = TSTORE ==> s' = tstore key x s /\ t' = tstore key y t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def]
QED

Theorem ld_shared_storage_write_backward:
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [a;v] /\
  ld_shared_state tn un s t /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  eval_operand v s = SOME x /\ eval_operand v t = SOME y /\
  word_agree_except (op_taint tn v INTER count 32) x y /\
  op_taint un v SUBSET op_taint tn v /\
  (i.inst_opcode = SSTORE ==> !addr. addr <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts addr).storage = (t.vs_accounts addr).storage) /\
  (i.inst_opcode = TSTORE ==> !addr. addr <> s.vs_call_ctx.cc_address ==>
    s.vs_transient addr = t.vs_transient addr) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by gvs[ld_shared_state_def] >>
  drule_all ld_storage_write_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >> gvs[]
  >- (`!addr. addr <> s.vs_call_ctx.cc_address ==>
          (s.vs_accounts addr).storage = (t.vs_accounts addr).storage` by metis_tac[] >>
      drule_all lowerDloadMaskedStorageTheory.ld_shared_sstore >>
      disch_then (qspec_then `key` mp_tac) >>
      simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
           ld_shared_state_def]) >>
  `!addr. addr <> s.vs_call_ctx.cc_address ==>
      s.vs_transient addr = t.vs_transient addr` by metis_tac[] >>
  drule_all lowerDloadMaskedStorageTheory.ld_shared_tstore >>
  disch_then (qspec_then `key` mp_tac) >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       ld_shared_state_def]
QED
