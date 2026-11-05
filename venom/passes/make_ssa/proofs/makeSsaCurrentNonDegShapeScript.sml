Theory makeSsaCurrentNonDegShape
Ancestors
  makeSsaCurrentNonDegCleanup makeSsaCurrentDefs makeSsaDefs venomWf venomInst list

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
