Theory o1FmpOpcodePreservation
Ancestors
  fmpLowerDefs fmpStepPredicateTransport fmpStepRewrite
  fmpStepRestrictionClosure callLayoutDefs venomInst list

Theorem fmp_lower_inst_opcode_absence[local]:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\ inst.inst_opcode <> op /\
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\j. j.inst_opcode <> op) out
Proof
  rpt strip_tac >>
  gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem fmp_lower_function_opcode_absence:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY (\j. j.inst_opcode <> op) (fn_insts fn) ==>
  EVERY (\j. j.inst_opcode <> op) (fn_insts fn')
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule fmp_lower_function_every >>
  disch_then (qspec_then `\j. j.inst_opcode <> op` mp_tac) >>
  (impl_tac >- (qpat_x_assum `op = _ \/ _` strip_assume_tac >> (rpt conj_tac
    >- fs[]
    >- (rpt strip_tac >> irule fmp_lower_inst_opcode_absence >>
        gvs[EVERY_MEM] >> metis_tac[])
    >- (rpt strip_tac >>
        drule_at (Pat `fmp_emit_restores _ _ _ = _`) fmp_emit_restores_every >>
        disch_then irule >> gvs[mk_inst_def]) >>
    rpt strip_tac >>
    gvs[fmp_make_root_layout_def, AllCaseEqs(), mk_inst_def,
        set_param_index_def, OPTION_TO_LIST_def] >>
    drule split_fmp_entry_retpc_restrictions >>
    rw[EVERY_MEM] >> gvs[OPTION_TO_LIST_def]))) >> simp[]
QED
