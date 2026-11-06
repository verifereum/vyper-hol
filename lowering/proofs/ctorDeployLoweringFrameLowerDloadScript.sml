Theory ctorDeployLoweringFrameLowerDload
Ancestors lowerDloadDefs venomInst

Theorem lower_dload_inst_supply_call_free[local]:
  lower_dload_inst_supply s inst = (insts,s') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) insts
Proof
  simp[lower_dload_inst_supply_def] >>
  Cases_on `inst.inst_opcode = DLOAD` >> simp[]
  >- (rpt CASE_TAC >> simp[] >> rpt strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES` >> simp[] >>
  rpt CASE_TAC >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_call_free[local]:
  !insts s outs s'.
  lower_dload_insts_supply s insts = (outs,s') /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) insts ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) outs
Proof
  Induct >> simp[Once lower_dload_insts_supply_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] lower_dload_inst_supply_call_free) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem lower_dload_block_supply_call_free[local]:
  lower_dload_block_supply s bb = (bb',s') /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb'.bb_instructions
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] lower_dload_insts_supply_call_free) >> simp[]
QED

Theorem lower_dload_blocks_supply_call_free[local]:
  !bbs s outs s'.
  lower_dload_blocks_supply s bbs = (outs,s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) outs
Proof
  Induct >> simp[Once lower_dload_blocks_supply_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] lower_dload_block_supply_call_free) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem lower_dload_function_supply_call_free:
  lower_dload_function_supply s fn = (fn',s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] lower_dload_blocks_supply_call_free) >> simp[]
QED
