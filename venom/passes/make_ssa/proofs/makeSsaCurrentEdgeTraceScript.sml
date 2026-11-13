Theory makeSsaCurrentEdgeTrace
Ancestors
  makeSsaDefs makeSsaCurrentProps cfgTransform cfgTransformProps venomInst
  list rich_list pair
  venomExecProofs

(* Positions refer to the immutable original predecessor/owner pair list. *)
Definition current_phi_slots_def:
  current_phi_slots slots = FLAT (MAP (\(l,v). [Label l; Var v]) slots)
End

Theorem current_phi_slots_update:
  !slots rs p.
  update_current_phi_for_pred rs p (current_phi_slots slots) =
  current_phi_slots (MAP (\(l,v). (l,if l = p then latest_current_name rs v else v)) slots)
Proof
  Induct >> simp[current_phi_slots_def, update_current_phi_for_pred_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_phi_slots_def, update_current_phi_for_pred_def] >>
  rpt gen_tac >> Cases_on `h0 = p` >> fs[current_phi_slots_def]
QED

Theorem current_phi_slots_other_pred:
  !slots rs p.
  EVERY (\(l,v). l <> p) slots ==>
  update_current_phi_for_pred rs p (current_phi_slots slots) = current_phi_slots slots
Proof
  Induct >> simp[current_phi_slots_def, update_current_phi_for_pred_def] >>
  gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def, update_current_phi_for_pred_def]
QED

Theorem current_phi_slots_commute:
  !slots rs rt p q.
  p <> q ==>
  update_current_phi_for_pred rs p
    (update_current_phi_for_pred rt q (current_phi_slots slots)) =
  update_current_phi_for_pred rt q
    (update_current_phi_for_pred rs p (current_phi_slots slots))
Proof
  Induct >> simp[current_phi_slots_def, update_current_phi_for_pred_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_phi_slots_def, update_current_phi_for_pred_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h0 = p` >> Cases_on `h0 = q` >>
  gvs[current_phi_slots_def, update_current_phi_for_pred_def]
QED

Theorem current_phi_output_rename_commutes:
  inst.inst_opcode = PHI /\ rename_current_inst s rs inst = (rs',s',inst') ==>
  rename_current_inst s rs
    (inst with inst_operands := update_current_phi_for_pred rt p inst.inst_operands) =
  (rs',s',inst' with inst_operands := update_current_phi_for_pred rt p inst.inst_operands)
Proof
  simp[rename_current_inst_def] >> strip_tac >>
  qpat_x_assum `_ = (rs',s',inst')` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[]
QED

Definition current_edge_inst_def:
  current_edge_inst rs p inst = if inst.inst_opcode <> PHI then inst
    else inst with inst_operands := update_current_phi_for_pred rs p inst.inst_operands
End

Definition current_edge_block_def:
  current_edge_block rs p bb =
    bb with bb_instructions := MAP (current_edge_inst rs p) bb.bb_instructions
End

Definition current_edge_step_def:
  current_edge_step rs p bbs l = case lookup_block l bbs of
    NONE => bbs
  | SOME bb => replace_block l (current_edge_block rs p bb) bbs
End

Theorem current_edge_block_label[simp]:
  (current_edge_block rs p bb).bb_label = bb.bb_label
Proof
  simp[current_edge_block_def]
QED

Theorem current_edge_step_lookup:
  lookup_block l (current_edge_step rs p bbs h) =
  OPTION_MAP (\bb. if l = h then current_edge_block rs p bb else bb)
    (lookup_block l bbs)
Proof
  simp[current_edge_step_def] >> Cases_on `lookup_block h bbs` >> simp[]
  >- (Cases_on `l = h` >> gvs[]) >>
  drule lookup_block_label >> strip_tac >> Cases_on `l = h` >> gvs[]
  >- (irule lookup_block_replace_eq >> simp[] >> metis_tac[]) >>
  irule lookup_block_replace_neq >> simp[]
QED

Theorem current_succ_phis_nil[simp]:
  update_current_succ_phis rs p bbs [] = bbs
Proof
  simp[update_current_succ_phis_def]
QED

Theorem current_succ_phis_cons:
  update_current_succ_phis rs p bbs (h::t) =
  update_current_succ_phis rs p (current_edge_step rs p bbs h) t
Proof
  simp[update_current_succ_phis_def, current_edge_step_def,
       current_edge_block_def, GSYM current_edge_inst_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem current_succ_phis_lookup:
  !succs bbs l rs p.
  ALL_DISTINCT succs ==>
  lookup_block l (update_current_succ_phis rs p bbs succs) =
  OPTION_MAP (\bb. if MEM l succs then current_edge_block rs p bb else bb)
    (lookup_block l bbs)
Proof
  Induct >> simp[current_succ_phis_cons] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[current_edge_step_lookup] >>
  Cases_on `lookup_block l bbs` >> simp[] >>
  Cases_on `l = h` >> Cases_on `MEM l succs` >> gvs[]
QED

Theorem current_edge_inst_outputs[simp]:
  (current_edge_inst rs p inst).inst_outputs = inst.inst_outputs
Proof
  simp[current_edge_inst_def] >> Cases_on `inst.inst_opcode = PHI` >> simp[]
QED

Theorem current_edge_block_outputs[simp]:
  MAP instruction_inst_outputs (current_edge_block rs p bb).bb_instructions =
    MAP instruction_inst_outputs bb.bb_instructions
Proof
  simp[current_edge_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem current_succ_phis_outputs:
  ALL_DISTINCT succs ==>
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions)
    (lookup_block l (update_current_succ_phis rs p bbs succs)) =
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions)
    (lookup_block l bbs)
Proof
  strip_tac >> drule current_succ_phis_lookup >>
  disch_then (qspecl_then [`bbs`, `l`, `rs`, `p`] mp_tac) >>
  strip_tac >> simp[] >> Cases_on `lookup_block l bbs` >> simp[] >>
  Cases_on `MEM l succs` >> simp[]
QED

Theorem current_succ_phis_selected:
  ALL_DISTINCT succs /\ MEM l succs /\ lookup_block l bbs = SOME bb ==>
  lookup_block l (update_current_succ_phis rs p bbs succs) =
    SOME (current_edge_block rs p bb)
Proof
  rpt strip_tac >> drule current_succ_phis_lookup >>
  disch_then (qspecl_then [`bbs`, `l`, `rs`, `p`] mp_tac) >> simp[]
QED

Theorem current_succ_phis_unselected:
  ALL_DISTINCT succs /\ ~MEM l succs ==>
  lookup_block l (update_current_succ_phis rs p bbs succs) = lookup_block l bbs
Proof
  rpt strip_tac >> drule current_succ_phis_lookup >>
  disch_then (qspecl_then [`bbs`, `l`, `rs`, `p`] mp_tac) >> simp[]
QED

Theorem current_edge_inst_slots:
  inst.inst_opcode = PHI /\ inst.inst_operands = current_phi_slots slots ==>
  (current_edge_inst rs p inst).inst_operands =
  current_phi_slots (MAP (\(l,v). (l,if l = p then latest_current_name rs v else v)) slots)
Proof
  simp[current_edge_inst_def, current_phi_slots_update]
QED

Theorem current_edge_inst_commute:
  inst.inst_opcode = PHI /\ inst.inst_operands = current_phi_slots slots /\ p <> q ==>
  current_edge_inst rs p (current_edge_inst rt q inst) =
  current_edge_inst rt q (current_edge_inst rs p inst)
Proof
  simp[current_edge_inst_def] >> rpt strip_tac >>
  simp[current_phi_slots_commute]
QED

Theorem current_edge_insts_commute:
  EVERY (\inst. inst.inst_opcode = PHI ==>
    ?slots. inst.inst_operands = current_phi_slots slots) insts /\ p <> q ==>
  MAP (current_edge_inst rs p) (MAP (current_edge_inst rt q) insts) =
  MAP (current_edge_inst rt q) (MAP (current_edge_inst rs p) insts)
Proof
  simp[MAP_MAP_o, EVERY_MEM] >> strip_tac >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM inst insts` >> Cases_on `inst.inst_opcode = PHI`
  >- (first_x_assum drule >> simp[] >> strip_tac >>
      irule current_edge_inst_commute >> metis_tac[]) >>
  simp[current_edge_inst_def]
QED

Theorem current_edge_block_commute:
  EVERY (\inst. inst.inst_opcode = PHI ==>
    ?slots. inst.inst_operands = current_phi_slots slots) bb.bb_instructions /\ p <> q ==>
  current_edge_block rs p (current_edge_block rt q bb) =
  current_edge_block rt q (current_edge_block rs p bb)
Proof
  strip_tac >> drule_all current_edge_insts_commute >>
  disch_then (qspecl_then [`rt`, `rs`] assume_tac) >>
  simp[current_edge_block_def] >> metis_tac[]
QED

Theorem current_phi_slots_length[simp]:
  !slots. LENGTH (current_phi_slots slots) = 2 * LENGTH slots
Proof
  Induct >> simp[current_phi_slots_def] >> gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def]
QED

Theorem current_phi_slots_index:
  !slots i. i < LENGTH slots ==>
  EL (2 * i) (current_phi_slots slots) = Label (FST (EL i slots)) /\
  EL (2 * i + 1) (current_phi_slots slots) = Var (SND (EL i slots))
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> Cases >>
  simp[current_phi_slots_def, arithmeticTheory.MULT_CLAUSES,
       arithmeticTheory.ADD_CLAUSES] >>
  `2 * n + 2 = SUC (SUC (2 * n))` by decide_tac >>
  `2 * n + 3 = SUC (SUC (2 * n + 1))` by decide_tac >>
  qpat_x_assum `2 * n + 2 = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `2 * n + 3 = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[EL] >> fs[current_phi_slots_def]
QED

Theorem current_phi_slots_updated_index:
  i < LENGTH slots ==>
  EL (2 * i + 1) (update_current_phi_for_pred rs p (current_phi_slots slots)) =
  Var (if FST (EL i slots) = p then latest_current_name rs (SND (EL i slots))
       else SND (EL i slots))
Proof
  strip_tac >> simp[current_phi_slots_update] >>
  qspec_then `MAP (\(l,v). (l,if l = p then latest_current_name rs v else v)) slots`
    (qspec_then `i` mp_tac) current_phi_slots_index >>
  simp[EL_MAP] >> Cases_on `EL i slots` >> simp[]
QED
