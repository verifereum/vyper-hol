Theory o1DloadOpcodePreservation
Ancestors
  lowerDloadDefs o1ContractLowerDload venomInst list

Theorem lower_dload_inst_supply_no_returndatacopy[local]:
  lower_dload_inst_supply s i = (xs,t) /\
  i.inst_opcode <> RETURNDATACOPY ==>
  EVERY (\j. j.inst_opcode <> RETURNDATACOPY) xs
Proof
  rpt strip_tac >> gvs[lower_dload_inst_supply_def, AllCaseEqs()]
QED

Theorem lower_dload_function_supply_no_returndatacopy:
  lower_dload_function_supply s fn = (fn',s') /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts fn')
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all lower_dload_function_supply_member >> strip_tac >>
  rename1 `MEM src (fn_insts fn)` >>
  `src.inst_opcode <> RETURNDATACOPY` by metis_tac[] >>
  drule_all lower_dload_inst_supply_no_returndatacopy >>
  disch_then assume_tac >> fs[EVERY_MEM] >> metis_tac[]
QED
