Theory o1MakeSsaPreparation
Ancestors
  makeSsaDefs venomInst list pair

Definition prepared_prefix_def:
  prepared_prefix old new <=> old.bb_label = new.bb_label /\
    ?pre. EVERY (\i. i.inst_opcode = PHI) pre /\
      new.bb_instructions = pre ++ old.bb_instructions
End

Theorem prepared_prefix_refl[simp]:
  prepared_prefix bb bb
Proof
  simp[prepared_prefix_def] >> qexists `[]` >> simp[]
QED

Theorem prepared_prefix_trans:
  prepared_prefix a b /\ prepared_prefix b c ==> prepared_prefix a c
Proof
  simp[prepared_prefix_def] >> rpt strip_tac >>
  qexists `pre' ++ pre` >> simp[]
QED

Theorem prepared_prefix_list_trans:
  !as bs cs. LIST_REL prepared_prefix as bs /\
    LIST_REL prepared_prefix bs cs ==> LIST_REL prepared_prefix as cs
Proof
  Induct >> Cases_on `bs` >> Cases_on `cs` >> simp[] >>
  metis_tac[prepared_prefix_trans]
QED

Theorem prepared_prefix_insert:
  phi.inst_opcode = PHI ==> prepared_prefix bb (insert_phi_at_block phi bb)
Proof
  simp[prepared_prefix_def, insert_phi_at_block_def] >>
  strip_tac >> qexists `[phi]` >> simp[]
QED

Theorem prepared_prefix_map_insert:
  phi.inst_opcode = PHI ==>
  LIST_REL prepared_prefix bbs
    (MAP (\bb. if bb.bb_label = f then insert_phi_at_block phi bb else bb) bbs)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  simp[EL_MAP] >> IF_CASES_TAC >> simp[prepared_prefix_insert]
QED

Theorem prepared_process_frontiers:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==> LIST_REL prepared_prefix bbs bbs'
Proof
  Induct >- simp[process_frontiers_supply_def, LIST_REL_EL_EQN] >>
  rpt gen_tac >> simp[process_frontiers_supply_def] >>
  IF_CASES_TAC >- (metis_tac[]) >>
  IF_CASES_TAC >- (metis_tac[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule prepared_prefix_list_trans >> goal_assum (drule_at Any) >>
  irule prepared_prefix_map_insert >> simp[build_phi_inst_supply_def]
QED

Theorem prepared_insert_var:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    LIST_REL prepared_prefix bbs bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >> rpt conj_tac
  >- simp[insert_phis_for_var_supply_def, LIST_REL_EL_EQN] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once insert_phis_for_var_supply_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `!frontiers. _` (mp_tac o SRULE []) >> simp[] >>
  strip_tac >> drule prepared_process_frontiers >> strip_tac >>
  metis_tac[prepared_prefix_list_trans]
QED

Theorem prepared_add_phi_nodes:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    LIST_REL prepared_prefix bbs bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def, LIST_REL_EL_EQN] >>
  Cases_on `h` >> rpt gen_tac >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule prepared_insert_var >> strip_tac >>
  metis_tac[prepared_prefix_list_trans]
QED

Theorem prepared_prefix_lookup:
  !olds news lbl old. LIST_REL prepared_prefix olds news /\
    lookup_block lbl olds = SOME old ==>
    ?new. lookup_block lbl news = SOME new /\ prepared_prefix old new
Proof
  Induct >> Cases_on `news` >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> strip_tac >>
  `h.bb_label = h'.bb_label` by fs[prepared_prefix_def] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem prepared_add_phi_lookup:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  lookup_block lbl bbs = SOME old ==>
  ?new pre. lookup_block lbl bbs' = SOME new /\
    new.bb_label = old.bb_label /\ EVERY (\i. i.inst_opcode = PHI) pre /\
    new.bb_instructions = pre ++ old.bb_instructions
Proof
  strip_tac >> drule prepared_add_phi_nodes >> strip_tac >>
  drule_all prepared_prefix_lookup >> simp[prepared_prefix_def] >> metis_tac[]
QED
