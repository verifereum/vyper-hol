Theory dftPacketReturnLocal
Ancestors
  dftIndexedExec dftGasFromListRestore venomExecSemantics
  venomInst venomState list

Theorem dft_packet_ret_step_restore:
  MEM i.inst_opcode [RET; RETFMP] /\
  step_inst f C i s = IntRet ir t ==>
  t = s /\
  step_inst g D i (s with vs_gas_readings := gs) =
    IntRet ir (s with vs_gas_readings := gs)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by gvs[] >>
  gvs[step_inst_non_invoke] >>
  `t = s` by
    (gvs[step_inst_base_def, AllCaseEqs()]) >>
  gvs[] >>
  `restore_rel gs (step_inst_base i s)
     (step_inst_base i (s with vs_gas_readings := gs))` by
    (irule step_base_restore >> simp[]) >>
  gvs[] >>
  Cases_on `step_inst_base i (s with vs_gas_readings := gs)` >>
  simp[restore_rel_def] >> strip_tac >> gvs[]
QED

Theorem dft_packet_fold_intret:
  !pre s u.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons f C) OK pre s = OK u /\
  step_inst f C term u = IntRet ir t ==>
  FOLDR (dft_exec_cons f C) OK (pre ++ [term]) s = IntRet ir t
Proof
  Induct >> simp[FOLDR, dft_exec_cons_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst f C h s` >> gvs[] >>
  first_x_assum irule >> simp[]
QED
