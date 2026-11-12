Theory lowerDloadEnvironmentRead
Ancestors
  lowerDloadReadEffects lowerDloadScalarClosure lowerDloadSharedState
  lowerDloadOwnership lowerDloadOperand lowerDloadPairedBoundary
  venomExecSemantics venomInst ptrDiscipline list words

Theorem ld_environment_read_backward:
  MEM i.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE] /\
  ld_shared_state tn un s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' out w. step_inst fuelS CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  strip_tac >> drule ld_shared_state_environment >> strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> strip_tac >>
  FIRST [drule_at (Pat `exec_read0 _ _ _ = _`) ld_exec_read0_backward,
         drule_at (Pat `exec_read1 _ _ _ = _`) ld_exec_read1_backward] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  qexists_tac `w` >> simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> simp[]
QED

Theorem ld_owned_environment_read_backward:
  MEM i.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE] /\
  ld_shared_state tn un s t /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  drule_all ld_environment_read_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >> gvs[] >>
  `!st ta. out_taint ta i st = {}` by
    (rpt gen_tac >> simp[out_taint_def] >>
     Cases_on `i.inst_operands` >- simp[] >>
     rename1 `h::ops` >> Cases_on `ops`
     >- (simp[] >> CASE_TAC >> simp[]) >>
     rename1 `h::h2::rest` >> Cases_on `rest` >> simp[] >>
     CASE_TAC >> simp[]) >>
  `ld_owned_value E NONE NONE {} {} w w` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def]
QED
