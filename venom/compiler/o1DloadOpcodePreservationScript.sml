Theory o1DloadOpcodePreservation
Ancestors
  lowerDloadDefs o1ContractLowerDload venomInst list

Theorem lower_dload_inst_supply_opcode_absence[local]:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
  lower_dload_inst_supply s i = (xs,t) /\
  i.inst_opcode <> op ==>
  EVERY (\j. j.inst_opcode <> op) xs
Proof
  rpt strip_tac >> gvs[lower_dload_inst_supply_def, AllCaseEqs()]
QED

Theorem lower_dload_function_supply_opcode_absence:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
  lower_dload_function_supply s fn = (fn',s') /\
  EVERY (\i. i.inst_opcode <> op) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> op) (fn_insts fn')
Proof
  simp[EVERY_MEM] >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >> rpt strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  rename1 `MEM src (fn_insts fn)` >>
  `src.inst_opcode <> op` by metis_tac[] >>
  drule_all lower_dload_inst_supply_opcode_absence >>
  disch_then assume_tac >> fs[EVERY_MEM] >> metis_tac[]
QED
