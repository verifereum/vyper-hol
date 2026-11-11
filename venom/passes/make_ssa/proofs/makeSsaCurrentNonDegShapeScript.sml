Theory makeSsaCurrentNonDegShape
Ancestors
  makeSsaCurrentNonDegCleanup makeSsaCurrentDefs makeSsaDefs venomWf venomInst list
  simplifyCfgStruct phiTransform

Theorem current_nondeg_canonical_operands:
  !preds. phi_well_formed (FLAT (MAP (\l. [Label l; Var v]) preds))
Proof
  Induct >> simp[phi_well_formed_def]
QED

Theorem current_nondeg_insert_shape:
  current_nondeg_block_shape bb /\ inst.inst_opcode = PHI /\
  phi_well_formed inst.inst_operands ==>
  current_nondeg_block_shape (insert_phi_at_block inst bb)
Proof
  simp[current_nondeg_block_shape_def, insert_phi_at_block_def] >>
  strip_tac >> rpt conj_tac >> simp[] >> rpt strip_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem current_nondeg_placement_map:
  !bbs f id v preds. EVERY current_nondeg_block_shape bbs ==>
  EVERY current_nondeg_block_shape
    (MAP (\bb. if bb.bb_label = f then
      insert_phi_at_block (build_phi_inst_supply id v preds) bb else bb) bbs)
Proof
  simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >> IF_CASES_TAC >> simp[] >>
  irule current_nondeg_insert_shape >>
  simp[build_phi_inst_supply_def, current_nondeg_canonical_operands]
QED

Theorem current_nondeg_frontiers_shape:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
  EVERY current_nondeg_block_shape bbs /\
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') ==>
  EVERY current_nondeg_block_shape bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  rpt gen_tac >> simp[Once process_frontiers_supply_def] >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >> irule current_nondeg_placement_map >> simp[]
QED

Theorem current_nondeg_var_placement_shape:
  !s v df pm li bbs wl hp.
  EVERY current_nondeg_block_shape bbs ==>
  !bbs' s'. insert_phis_for_var_supply s v df pm li bbs wl hp = (bbs',s') ==>
    EVERY current_nondeg_block_shape bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >> conj_tac
  >- simp[insert_phis_for_var_supply_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once insert_phis_for_var_supply_def] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> drule_all current_nondeg_frontiers_shape >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem current_nondeg_add_placement_shape:
  !defs s df pm li bbs bbs' s'.
  EVERY current_nondeg_block_shape bbs /\
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
  EVERY current_nondeg_block_shape bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once add_phi_nodes_supply_def] >> pairarg_tac >> simp[] >>
  strip_tac >> drule_all current_nondeg_var_placement_shape >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem current_nondeg_shape_transport:
  current_nondeg_block_shape bb /\
  LIST_REL (\a b. a.inst_opcode = b.inst_opcode /\
    (a.inst_opcode = PHI ==> phi_well_formed a.inst_operands ==>
      phi_well_formed b.inst_operands)) bb.bb_instructions insts ==>
  current_nondeg_block_shape (bb with bb_instructions := insts)
Proof
  simp[current_nondeg_block_shape_def, LIST_REL_EL_EQN, EVERY_EL] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem current_nondeg_update_operands:
  !ops. phi_well_formed ops ==>
    phi_well_formed (update_current_phi_for_pred rs p ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def, update_current_phi_for_pred_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[phi_well_formed_def]
QED

Theorem current_nondeg_rename_inst:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  inst.inst_opcode = inst'.inst_opcode /\
  (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands ==>
    phi_well_formed inst'.inst_operands)
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem current_nondeg_rename_insts:
  !insts s rs rs' s' insts'.
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  LIST_REL (\a b. a.inst_opcode = b.inst_opcode /\
    (a.inst_opcode = PHI ==> phi_well_formed a.inst_operands ==>
      phi_well_formed b.inst_operands)) insts insts'
Proof
  Induct >- simp[rename_current_block_insts_def] >> rpt gen_tac >>
  simp[Once rename_current_block_insts_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule current_nondeg_rename_inst >> strip_tac >> simp[] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem current_nondeg_rename_block_shape:
  current_nondeg_block_shape bb /\
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts) ==>
  current_nondeg_block_shape (bb with bb_instructions := insts)
Proof
  strip_tac >> irule current_nondeg_shape_transport >> simp[] >>
  irule current_nondeg_rename_insts >> goal_assum (drule_at Any)
QED

Theorem current_nondeg_edge_block_shape:
  current_nondeg_block_shape bb ==>
  current_nondeg_block_shape (bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst else
      inst with inst_operands := update_current_phi_for_pred rs p inst.inst_operands)
      bb.bb_instructions)
Proof
  strip_tac >> irule current_nondeg_shape_transport >> simp[] >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  Cases_on `(EL n bb.bb_instructions).inst_opcode = PHI` >>
  simp[current_nondeg_update_operands]
QED

Theorem current_nondeg_succs_shape:
  !succs bbs. EVERY current_nondeg_block_shape bbs ==>
  EVERY current_nondeg_block_shape (update_current_succ_phis rs p bbs succs)
Proof
  Induct >> fs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  irule current_nondeg_edge_block_shape >>
  drule lookup_block_MEM >> fs[EVERY_MEM]
QED

Theorem current_nondeg_local_replace_shape:
  EVERY current_nondeg_block_shape bbs /\ lookup_block l bbs = SOME bb /\
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts) ==>
  EVERY current_nondeg_block_shape
    (replace_block l (bb with bb_instructions := insts) bbs)
Proof
  strip_tac >> irule EVERY_replace_block >> simp[] >>
  irule current_nondeg_rename_block_shape >> conj_tac
  >- (drule lookup_block_MEM >> fs[EVERY_MEM]) >>
  metis_tac[]
QED

Theorem current_nondeg_rename_shape:
  (!s rs bbs sm tree. EVERY current_nondeg_block_shape bbs ==>
    !ctrs s' bbs'. rename_current_blocks s rs bbs sm tree = (ctrs,s',bbs') ==>
      EVERY current_nondeg_block_shape bbs') /\
  (!s ctrs stacks bbs sm trees. EVERY current_nondeg_block_shape bbs ==>
    !ctrs' s' bbs'. rename_current_children s ctrs stacks bbs sm trees = (ctrs',s',bbs') ==>
      EVERY current_nondeg_block_shape bbs')
Proof
  ho_match_mp_tac rename_current_blocks_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      simp[Once rename_current_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >>
      pairarg_tac >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      irule current_nondeg_succs_shape >>
      irule current_nondeg_local_replace_shape >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once rename_current_blocks_def] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
