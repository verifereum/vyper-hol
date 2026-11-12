Theory o1CfgOpcodePreservation
Ancestors
  cfgNormDefs cfgNormSupplyProofs cfgNormSupplySim cfgTransform
  cfgTransformProps venomInst ctxLookupAgreeHelpers list
Libs
  pairLib

Theorem cfg_subst_opcode_predicate[local]:
  EVERY (\i. P i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. P i.inst_opcode)
    (subst_label_terminator old new bb).bb_instructions
Proof
  rewrite_tac[GSYM EVERY_MAP] >>
  rewrite_tac[CONV_RULE (DEPTH_CONV ETA_CONV) supply_subst_terminator_opcodes]
QED

Theorem cfg_phis_opcode_predicate[local]:
  EVERY (\i. P i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. P i.inst_opcode)
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  rewrite_tac[GSYM EVERY_MAP] >>
  rewrite_tac[CONV_RULE (DEPTH_CONV ETA_CONV) supply_update_phis_opcodes]
QED

Theorem cfg_replace_opcode_predicate[local]:
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) blocks /\
  EVERY (\i. P i.inst_opcode) new_bb.bb_instructions ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions)
    (replace_block lbl new_bb blocks)
Proof
  rewrite_tac[replace_block_def, EVERY_MAP] >> strip_tac >>
  irule EVERY_MONOTONIC >>
  qexists `\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  Cases_on `x.bb_label = lbl` >> simp[]
QED

Theorem cfg_split_opcode_predicate[local]:
  P ASSIGN /\ P JMP /\
  build_split_block_supply s pred target = (split,repls,s') ==>
  EVERY (\i. P i.inst_opcode) split.bb_instructions
Proof
  strip_tac >> drule supply_split_opcodes >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem cfg_insert_split_opcode_predicate[local]:
  P ASSIGN /\ P JMP /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn.fn_blocks /\
  EVERY (\i. P i.inst_opcode) pred.bb_instructions /\
  EVERY (\i. P i.inst_opcode) target.bb_instructions /\
  insert_split_supply s fn pred target = (fn',s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn'.fn_blocks
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  `EVERY (\i. P i.inst_opcode) split.bb_instructions` by
    metis_tac[cfg_split_opcode_predicate] >>
  `EVERY (\i. P i.inst_opcode)
    (subst_label_terminator target.bb_label split.bb_label pred).bb_instructions` by
    metis_tac[cfg_subst_opcode_predicate] >>
  reverse conj_tac >- simp[] >>
  irule cfg_replace_opcode_predicate >> conj_tac
  >- (irule cfg_replace_opcode_predicate >> simp[]) >>
  irule cfg_phis_opcode_predicate >>
  Cases_on `pred.bb_label = target.bb_label` >> simp[]
QED

Theorem cfg_find_split_opcode_predicate[local]:
  !bbs fn s fn' changed s'.
  P ASSIGN /\ P JMP /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn.fn_blocks /\
  EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
  find_and_split_supply fn s bbs = (fn',changed,s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn'.fn_blocks
Proof
  rpt gen_tac >> strip_tac >>
  drule find_and_split_supply_cases >> strip_tac >- gvs[] >>
  irule cfg_insert_split_opcode_predicate >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem cfg_round_opcode_predicate[local]:
  P ASSIGN /\ P JMP /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn.fn_blocks /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn'.fn_blocks
Proof
  strip_tac >> gvs[cfg_norm_round_supply_def] >>
  irule cfg_find_split_opcode_predicate >> simp[] >>
  goal_assum (drule_at Any) >> simp[EVERY_MEM]
QED

Theorem cfg_iter_opcode_predicate[local]:
  !n s fn fn' s'.
  P ASSIGN /\ P JMP /\
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn.fn_blocks /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) fn'.fn_blocks
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def] >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >>
  metis_tac[cfg_round_opcode_predicate]
QED

Theorem cfg_norm_function_supply_opcode_predicate:
  P ASSIGN /\ P JMP /\
  (!i. MEM i (fn_insts fn) ==> P i.inst_opcode) ==>
  !i. MEM i (fn_insts (FST (cfg_norm_function_supply s fn))) ==> P i.inst_opcode
Proof
  simp[GSYM EVERY_MEM, fn_insts_def, fn_insts_EVERY_block,
       cfg_norm_function_supply_def] >>
  Cases_on `cfg_norm_iter_supply (2 * LENGTH fn.fn_blocks) s fn` >>
  simp[] >> metis_tac[cfg_iter_opcode_predicate]
QED

Theorem cfg_norm_function_supply_no_returndatacopy:
  (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> RETURNDATACOPY) ==>
  !i. MEM i (fn_insts (FST (cfg_norm_function_supply s fn))) ==>
      i.inst_opcode <> RETURNDATACOPY
Proof
  strip_tac >> ho_match_mp_tac cfg_norm_function_supply_opcode_predicate >> simp[]
QED
