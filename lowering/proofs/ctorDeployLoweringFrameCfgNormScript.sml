Theory ctorDeployLoweringFrameCfgNorm
Ancestors cfgNormDefs cfgTransform venomInst venomPassDispatcher

Theorem build_forwarding_assigns_supply_call_free[local]:
  !vars s repls insts s'.
  build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) insts
Proof
  Induct >> simp[Once build_forwarding_assigns_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem build_split_block_supply_call_free[local]:
  build_split_block_supply s pred target = (bb,repls,s') ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions
Proof
  simp[build_split_block_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule build_forwarding_assigns_supply_call_free >> simp[]
QED

Theorem subst_label_terminator_call_free[local]:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
    (subst_label_terminator old new bb).bb_instructions
Proof
  simp[subst_label_terminator_def] >>
  simp[listTheory.EVERY_MAP, COND_RAND, subst_label_inst_def]
QED

Theorem update_phis_for_split_call_free[local]:
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def] >>
  simp[listTheory.EVERY_MAP, COND_RAND] >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> gvs[] >> metis_tac[]
QED

Theorem replace_block_call_free[local]:
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) bbs /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb'.bb_instructions ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions)
    (replace_block lbl bb' bbs)
Proof
  simp[replace_block_def] >> simp[listTheory.EVERY_MAP] >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `bb.bb_label = lbl` >> gvs[] >> metis_tac[]
QED

Theorem insert_split_supply_call_free[local]:
  insert_split_supply s fn pred target = (fn',s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) pred.bb_instructions /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) target.bb_instructions ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  simp[insert_split_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule build_split_block_supply_call_free >> strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
    (subst_label_terminator target.bb_label split_bb.bb_label pred).bb_instructions` by
    (irule subst_label_terminator_call_free >> simp[]) >> gvs[] >>
  irule (SRULE [] replace_block_call_free) >> conj_tac
  >- (irule (SRULE [] replace_block_call_free) >> simp[]) >>
  irule (SRULE [] update_phis_for_split_call_free) >>
  IF_CASES_TAC >> simp[]
QED

Theorem find_some_mem[local]:
  !P xs x. FIND P xs = SOME x ==> MEM x xs
Proof
  gen_tac >> Induct >> simp[listTheory.FIND_thm] >>
  rpt gen_tac >> Cases_on `P h` >> gvs[]
QED

Theorem find_and_split_supply_call_free[local]:
  !bbs fn s fn' changed s'.
  find_and_split_supply fn s bbs = (fn',changed,s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  Induct >> simp[Once find_and_split_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >> gvs[] >> first_x_assum irule >> metis_tac[]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (first_x_assum irule >> metis_tac[]) >>
  drule find_some_mem >>
  simp[block_preds_def, listTheory.MEM_FILTER] >> strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) pred_bb.bb_instructions` by
    (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[] >> drule_all (SRULE [] insert_split_supply_call_free) >> simp[]
QED

Theorem cfg_norm_iter_supply_call_free[local]:
  !fuel s fn fn' s'.
  cfg_norm_iter_supply fuel s fn = (fn',s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  Induct >> simp[Once cfg_norm_iter_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[cfg_norm_round_supply_def] >>
  drule_all (SRULE [] find_and_split_supply_call_free) >> strip_tac >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem cfg_norm_function_supply_call_free:
  cfg_norm_function_supply s fn = (fn',s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  simp[cfg_norm_function_supply_def] >>
  MATCH_ACCEPT_TAC (SRULE [] cfg_norm_iter_supply_call_free)
QED

Theorem execute_configured_cfg_normalization_call_free:
  execute_configured_fn_pass rpolicy (CFP_Simple VP_CFGNormalization) unit s fn = SOME out /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) out.fpo_function.fn_blocks
Proof
  simp[execute_configured_fn_pass_cfg_normalization, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] cfg_norm_function_supply_call_free) >> simp[]
QED
