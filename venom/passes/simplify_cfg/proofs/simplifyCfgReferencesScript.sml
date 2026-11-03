(* Local reference closure and inert batch substitutions. *)
Theory simplifyCfgReferences
Ancestors
  simplifyCfgPhiShape o1PassContract cfgTransformProps venomExecProps
  list rich_list alist cfgTransform venomInst venomWf unitShapeDefs
  unitLabelMapIdentity

Theorem subst_block_labels_fn_identity:
  (!i l. MEM i (fn_insts f) /\ is_block_label_opcode i.inst_opcode /\
    MEM (Label l) i.inst_operands ==> MEM l (fn_labels f)) /\
  (!s t. MEM (s,t) lm ==> ~MEM s (fn_labels f)) ==>
  subst_block_labels_fn lm f = f
Proof
  strip_tac >>
  `!i. MEM i (fn_insts f) ==> subst_block_labels_inst lm i = i` by
    (rpt strip_tac >> simp[subst_block_labels_inst_def] >>
     Cases_on `is_block_label_opcode i.inst_opcode` >> simp[] >>
     irule subst_label_map_inst_id >> rpt strip_tac >>
     gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  simp[subst_block_labels_fn_def, ir_function_component_equality] >>
  irule MAP_eq_self >> rpt strip_tac >>
  simp[subst_block_labels_block_def, basic_block_component_equality] >>
  irule MAP_eq_self >> rpt strip_tac >>
  first_x_assum irule >> simp[fn_insts_MEM] >> metis_tac[]
QED

Theorem bb_terminator_label_successor:
  bb_well_formed bb /\ MEM i bb.bb_instructions /\
  is_terminator i.inst_opcode /\ MEM (Label l) i.inst_operands ==>
  MEM l (bb_succs bb)
Proof
  strip_tac >>
  `?n. n < LENGTH bb.bb_instructions /\ i = EL n bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  `i = LAST bb.bb_instructions` by
    (gvs[bb_well_formed_def] >> metis_tac[LAST_EL]) >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[bb_succs_def, MEM_nub, MEM_REVERSE, get_successors_def] >>
  simp[MEM_MAP, MEM_FILTER] >>
  qexists_tac `SOME l` >> simp[] >> qexists_tac `Label l` >>
  simp[venomStateTheory.get_label_def]
QED

Theorem phi_preds_block_labels:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  MEM i (fn_insts f) /\ is_block_label_opcode i.inst_opcode /\
  MEM (Label l) i.inst_operands ==> MEM l (fn_labels f)
Proof
  simp[fn_insts_MEM, is_block_label_opcode_def] >> strip_tac
  >- (`bb_well_formed bb` by gvs[EVERY_MEM] >>
      drule_all bb_terminator_label_successor >>
      metis_tac[fn_succs_closed_def]) >>
  `MEM l (pred_labels f bb.bb_label)` by metis_tac[] >>
  gvs[pred_labels_mem, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem label_positions_default[local]:
  i.inst_opcode <> JMP /\ i.inst_opcode <> JNZ /\
  i.inst_opcode <> PHI /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> ADD /\ i.inst_opcode <> CODECOPY ==>
  (label_positions_ok i <=>
   EVERY (\op. ~is_label_operand op) i.inst_operands)
Proof
  strip_tac >> simp[label_positions_ok_def] >>
  Cases_on `i.inst_opcode` >> gvs[]
QED

Theorem label_positions_codecopy[local]:
  label_positions_ok i /\ i.inst_opcode = CODECOPY /\
  MEM (Label l) i.inst_operands ==>
  l = "runtime_begin"
Proof
  rw[label_positions_ok_def] >> gvs[AllCaseEqs(), EVERY_MEM] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem label_positions_block_or_reserved:
  label_positions_ok i /\ i.inst_opcode <> INVOKE /\
  MEM (Label l) i.inst_operands ==>
  is_block_label_opcode i.inst_opcode \/ reserved_label l
Proof
  strip_tac >>
  Cases_on `i.inst_opcode = JMP`
  >- simp[is_block_label_opcode_def, is_terminator_def] >>
  Cases_on `i.inst_opcode = JNZ`
  >- simp[is_block_label_opcode_def, is_terminator_def] >>
  Cases_on `i.inst_opcode = PHI`
  >- simp[is_block_label_opcode_def] >>
  Cases_on `i.inst_opcode = ADD`
  >- (gvs[label_positions_ok_def, EVERY_MEM] >>
      Cases_on `i.inst_operands` >- gvs[] >>
      rename1 `i.inst_operands = h::rest` >>
      Cases_on `rest` >- gvs[stackPlanTypesTheory.is_label_operand_def] >>
      rename1 `i.inst_operands = h::second::tail` >>
      Cases_on `second` >> Cases_on `tail` >>
      gvs[stackPlanTypesTheory.is_label_operand_def, reserved_label_def] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `i.inst_opcode = CODECOPY`
  >- (disj2_tac >> drule_all label_positions_codecopy >>
      simp[reserved_label_def]) >>
  drule_all label_positions_default >>
  gvs[EVERY_MEM] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem phi_preds_label_refs_ok:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY label_positions_ok (fn_insts f) /\ fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) ==> fn_label_refs_ok f
Proof
  strip_tac >> simp[fn_label_refs_ok_def] >> rpt strip_tac >>
  rename1 `MEM i (fn_insts f)` >>
  `label_positions_ok i` by gvs[EVERY_MEM] >>
  drule_all label_positions_block_or_reserved >> strip_tac >> simp[] >>
  disj1_tac >> irule phi_preds_block_labels >> metis_tac[]
QED

Theorem phi_preds_subst_block_labels_identity:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\ fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  (!s t. MEM (s,t) lm ==> ~MEM s (fn_labels f)) ==>
  subst_block_labels_fn lm f = f
Proof
  strip_tac >> irule subst_block_labels_fn_identity >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule phi_preds_block_labels >> metis_tac[]
QED
