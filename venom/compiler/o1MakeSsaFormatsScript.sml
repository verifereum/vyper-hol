Theory o1MakeSsaFormats
Ancestors
  o1MakeSsaFrontier o1MakeSsaCfg makeSsaCurrentDefs unitShapeDefs
  venomInst stackPlanTypes list o1ContractSueStep simplifyCfgStruct
  cfgNormSupplySim venomWf fmpStepChunk fmpStepList

Theorem rename_current_operands_length:
  !ops. LENGTH (rename_current_operands rs ops) = LENGTH ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def]
QED

Theorem rename_current_operands_nonlabels:
  !ops. EVERY (\op. ~is_label_operand op) (rename_current_operands rs ops) =
        EVERY (\op. ~is_label_operand op) ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, is_label_operand_def]
QED

Theorem inst_shape_ok_outputs[simp]:
  inst_shape_ok (inst with inst_outputs := outs) = inst_shape_ok inst
Proof
  rewrite_tac[inst_shape_ok_def, label_positions_ok_def] >> simp[]
QED

Theorem rename_current_inst_shape:
  rename_current_inst s rs inst = (rs',s',inst') /\ inst_shape_ok inst ==>
  inst_shape_ok inst'
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  `inst with <|inst_operands := rename_current_operands rs inst.inst_operands;
               inst_outputs := outs'|> =
   (inst with inst_operands := rename_current_operands rs inst.inst_operands)
     with inst_outputs := outs'` by simp[] >>
  pop_assum SUBST1_TAC >> simp[] >>
  irule sue_inst_shape_projection >> simp[rename_current_operands_labels]
QED

Theorem rename_current_block_insts_shape:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') /\
    EVERY inst_shape_ok insts ==> EVERY inst_shape_ok insts'
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_current_inst_shape] >>
  first_x_assum drule_all >> simp[]
QED

Theorem update_current_phi_for_pred_pair_labels:
  !rs lbl ops.
    MAP FST (phi_pairs (update_current_phi_for_pred rs lbl ops)) =
    MAP FST (phi_pairs ops)
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def, phi_pairs_def] >>
  gvs[phi_pairs_def]
QED

Theorem update_current_phi_inst_shape:
  inst_shape_ok inst /\ inst.inst_opcode = PHI ==>
  inst_shape_ok (inst with inst_operands :=
    update_current_phi_for_pred rs lbl inst.inst_operands)
Proof
  strip_tac >>
  `LENGTH (phi_pairs (update_current_phi_for_pred rs lbl inst.inst_operands)) =
   LENGTH (phi_pairs inst.inst_operands)` by
    metis_tac[update_current_phi_for_pred_pair_labels, LENGTH_MAP] >>
  gvs[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
      update_current_phi_for_pred_pair_labels]
QED

Theorem update_current_succ_phis_shape:
  !succs bbs. EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions)
      (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >- metis_tac[] >> simp[] >>
  irule update_current_phi_inst_shape >> metis_tac[]
QED

Theorem rename_current_blocks_shape:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs')
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_shape >>
      irule EVERY_replace_block >> simp[] >>
      drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
      drule rename_current_block_insts_shape >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_raw_shape:
  inst_shape_ok inst ==> inst_shape_ok (simplify_current_phi_raw inst)
Proof
  strip_tac >> simp[simplify_current_phi_raw_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
  simp[] >> Cases_on `x'`
  >- simp[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def] >>
  simp[] >> IF_CASES_TAC >>
  simp[inst_shape_ok_def, label_positions_ok_def, is_read0_opcode_def,
       is_label_operand_def]
QED

Theorem simplify_current_phi_shape:
  inst_shape_ok inst ==> inst_shape_ok (simplify_current_phi inst)
Proof
  strip_tac >> simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_raw_shape]
QED

Theorem inst_shape_ok_id[simp]:
  inst_shape_ok (inst with inst_id := id) = inst_shape_ok inst
Proof
  rewrite_tac[inst_shape_ok_def, label_positions_ok_def] >> simp[]
QED

Theorem reassign_current_inst_ids_shape:
  !ids insts. EVERY inst_shape_ok insts ==>
    EVERY inst_shape_ok (reassign_current_inst_ids ids insts)
Proof
  Induct_on `ids` >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_prefix_parts_shape:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    EVERY inst_shape_ok insts ==>
    EVERY inst_shape_ok phis /\ EVERY inst_shape_ok ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  simp[simplify_current_phi_shape]
QED

Theorem simplify_current_phi_prefix_shape:
  EVERY inst_shape_ok insts ==>
  EVERY inst_shape_ok (simplify_current_phi_prefix insts)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule reassign_current_inst_ids_shape >> simp[EVERY_APPEND] >>
  drule_all simplify_current_phi_prefix_parts_shape >> simp[]
QED

Theorem simplify_current_phi_block_shape:
  EVERY inst_shape_ok bb.bb_instructions ==>
  EVERY inst_shape_ok (simplify_current_phi_block bb).bb_instructions
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_shape]
QED

Theorem simplify_current_phis_if_shape:
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[simplify_current_phi_block_shape, EVERY_MEM]
QED

Theorem make_ssa_current_fn_inst_shape:
  make_ssa_current_fn s fn = (fn',s') /\
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) fn'.fn_blocks
Proof
  Cases_on `fn_entry_label fn`
  >- (simp[make_ssa_current_fn_def] >> strip_tac >> gvs[]) >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  irule simplify_current_phis_if_shape >>
  drule (CONJUNCT1 rename_current_blocks_shape) >> disch_then irule >>
  `EVERY (\bb. MEM bb.bb_label (fn_labels fn) /\
    EVERY inst_shape_ok bb.bb_instructions) bbs1` by
    (drule (SRULE[current_frontier_map_def, current_pred_map_def, LET_THM]
              add_phi_nodes_supply_shape) >> disch_then irule >>
     gvs[EVERY_MEM, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem rename_current_inst_opcode:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  inst'.inst_opcode = inst.inst_opcode
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[]
QED

Theorem rename_current_block_insts_opcodes:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    MAP (\i. i.inst_opcode) insts' = MAP (\i. i.inst_opcode) insts
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_current_inst_opcode] >>
  first_x_assum drule >> simp[]
QED

Theorem rename_current_block_insts_well_formed:
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts') /\
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions := insts')
Proof
  strip_tac >> irule supply_bb_well_formed_opcodes >>
  qexists `bb` >> simp[] >>
  drule rename_current_block_insts_opcodes >> simp[]
QED

Theorem update_current_succ_phis_well_formed:
  !succs bbs. EVERY bb_well_formed bbs ==>
    EVERY bb_well_formed (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  irule cfgTransformPropsTheory.bb_well_formed_map_classification >>
  conj_tac >- (gen_tac >> Cases_on `inst.inst_opcode = PHI` >> simp[]) >>
  metis_tac[EVERY_MEM]
QED

Theorem rename_current_blocks_well_formed:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY bb_well_formed bbs ==> EVERY bb_well_formed bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY bb_well_formed bbs ==> EVERY bb_well_formed bbs')
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_well_formed >>
      irule EVERY_replace_block >> simp[] >>
      drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
      irule rename_current_block_insts_well_formed >>
      conj_tac >- metis_tac[EVERY_MEM] >>
      goal_assum (drule_at Any))
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_classification:
  inst.inst_opcode = PHI ==>
  MEM (simplify_current_phi inst).inst_opcode [PHI; ASSIGN; NOP]
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >> strip_tac >>
  IF_CASES_TAC >> simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
  simp[] >> Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem simplify_current_phi_prefix_parts_partition:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    list_prefix (\i. i.inst_opcode = PHI) insts ==>
    EVERY (\i. i.inst_opcode = PHI) phis /\
    EVERY (\i. i.inst_opcode <> PHI) ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[list_prefix_def] >> metis_tac[]) >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> strip_tac >>
  gvs[list_prefix_def]
QED

Theorem simplify_current_phi_nonterminal:
  inst.inst_opcode = PHI ==>
  ~is_terminator (simplify_current_phi inst).inst_opcode
Proof
  strip_tac >> drule simplify_current_phi_classification >>
  simp[] >> strip_tac >> gvs[is_terminator_def]
QED

Theorem simplify_current_phi_prefix_parts_terminal:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    list_terminal (\i. is_terminator i.inst_opcode) insts ==>
    EVERY (\i. ~is_terminator i.inst_opcode) phis /\
    list_terminal (\i. is_terminator i.inst_opcode) ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def, list_terminal_def] >>
  rpt gen_tac >> IF_CASES_TAC
  >- (strip_tac >> gvs[list_terminal_def]) >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> strip_tac >>
  gvs[list_terminal_def, is_terminator_def] >>
  `insts <> []` by (Cases_on `insts` >> gvs[list_terminal_def, is_terminator_def]) >>
  gvs[] >>
  `ordinary' <> []` by (Cases_on `ordinary'` >> gvs[list_terminal_def]) >>
  simp[list_terminal_def, simplify_current_phi_nonterminal]
QED

Theorem reassign_current_inst_ids_opcodes:
  !ids insts. MAP (\i. i.inst_opcode) (reassign_current_inst_ids ids insts) =
    MAP (\i. i.inst_opcode) insts
Proof
  Induct_on `ids` >> Cases_on `insts` >>
  simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_prefix_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    simplify_current_phi_prefix bb.bb_instructions)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule supply_bb_well_formed_opcodes >>
  qexists `bb with bb_instructions := phis ++ ordinary` >>
  simp[reassign_current_inst_ids_opcodes] >>
  qpat_x_assum `bb_well_formed bb` mp_tac >>
  simp[bb_well_formed_list] >> strip_tac >>
  drule_all simplify_current_phi_prefix_parts_partition >> strip_tac >>
  drule_all simplify_current_phi_prefix_parts_terminal >> strip_tac >>
  `ordinary <> []` by (Cases_on `ordinary` >> gvs[list_terminal_def]) >>
  simp[list_terminal_append, list_prefix_append, list_prefix_every,
       list_prefix_none] >>
  metis_tac[EVERY_MEM]
QED

Theorem simplify_current_phi_block_well_formed:
  bb_well_formed bb ==> bb_well_formed (simplify_current_phi_block bb)
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[] >>
  metis_tac[simplify_current_phi_prefix_well_formed]
QED

Theorem simplify_current_phis_if_well_formed:
  EVERY bb_well_formed bbs ==>
  EVERY bb_well_formed (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[simplify_current_phi_block_well_formed]
QED

Theorem make_ssa_current_fn_blocks_well_formed:
  make_ssa_current_fn s fn = (fn',s') /\
  EVERY bb_well_formed fn.fn_blocks ==>
  EVERY bb_well_formed fn'.fn_blocks
Proof
  Cases_on `fn_entry_label fn`
  >- (simp[make_ssa_current_fn_def] >> strip_tac >> gvs[]) >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  irule simplify_current_phis_if_well_formed >>
  drule (CONJUNCT1 rename_current_blocks_well_formed) >> disch_then irule >>
  drule (SRULE[current_frontier_map_def, current_pred_map_def, LET_THM]
            add_phi_nodes_supply_well_formed) >> disch_then irule >>
  gvs[EVERY_MEM, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem rename_current_outputs_length:
  !vs s rs rs' s' outs.
    rename_current_outputs s rs vs = (rs',s',outs) ==>
    LENGTH outs = LENGTH vs
Proof
  Induct >> simp[rename_current_outputs_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem inst_wf_output_length:
  LENGTH outs = LENGTH inst.inst_outputs ==>
  (inst_wf (inst with inst_outputs := outs) = inst_wf inst)
Proof
  strip_tac >>
  ` (outs = []) = (inst.inst_outputs = [])` by metis_tac[LENGTH_NIL] >>
  simp[inst_wf_def] >> Cases_on `inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_outputs = []` >> gvs[] >>
  simp[dretShapeDefsTheory.parse_dret_shape_def]
QED

Theorem rename_current_operands_inst_wf:
  inst_wf inst /\ inst.inst_opcode <> PHI ==>
  inst_wf (inst with inst_operands := rename_current_operands rs inst.inst_operands)
Proof
  strip_tac >> qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def, rename_current_operands_length] >>
  Cases_on `inst.inst_opcode` >> simp[] >> rpt strip_tac >>
  gvs[rename_current_operands_def, rename_current_operands_length]
  >- (Cases_on `c` >> simp[rename_current_operands_def])
  >- (Cases_on `sel` >> simp[rename_current_operands_def] >>
      rewrite_tac[GSYM EVERY_MAP, rename_current_operands_labels] >>
      gvs[EVERY_MAP])
  >- (Cases_on `inst.inst_operands` >>
      gvs[dretShapeDefsTheory.parse_dret_shape_def, rename_current_operands_def] >>
      Cases_on `h` >>
      gvs[dretShapeDefsTheory.parse_dret_shape_def, rename_current_operands_def,
          rename_current_operands_length]) >>
  metis_tac[rename_current_operands_length, LENGTH_NIL]
QED

Theorem rename_current_inst_wf:
  rename_current_inst s rs inst = (rs',s',inst') /\ inst_wf inst ==>
  inst_wf inst'
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule rename_current_outputs_length >> strip_tac
  >- (irule (iffRL inst_wf_output_length) >> simp[])
  >> `inst with <|inst_operands := rename_current_operands rs inst.inst_operands;
                 inst_outputs := outs'|> =
      (inst with inst_operands := rename_current_operands rs inst.inst_operands)
        with inst_outputs := outs'` by simp[] >>
  pop_assum SUBST1_TAC >>
  `inst_wf (inst with inst_operands := rename_current_operands rs inst.inst_operands)`
    by (irule rename_current_operands_inst_wf >> simp[]) >>
  qspecl_then [`outs'`,
    `inst with inst_operands := rename_current_operands rs inst.inst_operands`]
    mp_tac (GEN_ALL inst_wf_output_length) >> simp[]
QED

Theorem rename_current_block_insts_wf:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') /\
    EVERY inst_wf insts ==> EVERY inst_wf insts'
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_current_inst_wf] >>
  first_x_assum drule_all >> simp[]
QED

Theorem update_current_phi_for_pred_wf:
  !rs lbl ops. phi_well_formed ops ==>
    phi_well_formed (update_current_phi_for_pred rs lbl ops)
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def, phi_well_formed_def] >>
  gvs[phi_well_formed_def]
QED

Theorem update_current_phi_for_pred_length:
  !rs lbl ops. LENGTH (update_current_phi_for_pred rs lbl ops) = LENGTH ops
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def]
QED

Theorem update_current_phi_inst_wf:
  inst_wf inst /\ inst.inst_opcode = PHI ==>
  inst_wf (inst with inst_operands :=
    update_current_phi_for_pred rs lbl inst.inst_operands)
Proof
  strip_tac >> gvs[inst_wf_def, update_current_phi_for_pred_wf]
QED

Theorem update_current_succ_phis_wf:
  !succs bbs. EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions)
      (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >- metis_tac[] >> simp[] >>
  irule update_current_phi_inst_wf >> metis_tac[]
QED

Theorem rename_current_blocks_wf:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs')
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_wf >>
      irule EVERY_replace_block >> simp[] >>
      drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
      drule rename_current_block_insts_wf >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_raw_wf:
  inst_wf inst ==> inst_wf (simplify_current_phi_raw inst)
Proof
  strip_tac >> simp[simplify_current_phi_raw_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
  simp[] >> Cases_on `x'`
  >- simp[inst_wf_def] >>
  simp[] >> IF_CASES_TAC >> gvs[inst_wf_def]
QED

Theorem simplify_current_phi_wf:
  inst_wf inst ==> inst_wf (simplify_current_phi inst)
Proof
  strip_tac >> simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_raw_wf]
QED

Theorem inst_wf_id[simp]:
  inst_wf (inst with inst_id := id) = inst_wf inst
Proof
  rewrite_tac[inst_wf_def, dretShapeDefsTheory.parse_dret_shape_def] >> simp[]
QED

Theorem reassign_current_inst_ids_wf:
  !ids insts. EVERY inst_wf insts ==>
    EVERY inst_wf (reassign_current_inst_ids ids insts)
Proof
  Induct_on `ids` >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_prefix_parts_wf:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    EVERY inst_wf insts ==>
    EVERY inst_wf phis /\ EVERY inst_wf ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  simp[simplify_current_phi_wf]
QED

Theorem simplify_current_phi_prefix_wf:
  EVERY inst_wf insts ==> EVERY inst_wf (simplify_current_phi_prefix insts)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule reassign_current_inst_ids_wf >> simp[EVERY_APPEND] >>
  drule_all simplify_current_phi_prefix_parts_wf >> simp[]
QED

Theorem simplify_current_phi_block_wf:
  EVERY inst_wf bb.bb_instructions ==>
  EVERY inst_wf (simplify_current_phi_block bb).bb_instructions
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_wf]
QED

Theorem simplify_current_phis_if_wf:
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[simplify_current_phi_block_wf, EVERY_MEM]
QED

Theorem build_phi_inst_supply_wf:
  !preds. inst_wf (build_phi_inst_supply id var preds)
Proof
  simp[inst_wf_def, build_phi_inst_supply_def] >>
  Induct >> simp[phi_well_formed_def]
QED

Theorem add_phi_nodes_supply_wf:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  simp[makeSsaDefsTheory.insert_phi_at_block_def, build_phi_inst_supply_wf]
QED

Theorem make_ssa_current_fn_inst_wf:
  make_ssa_current_fn s fn = (fn',s') /\ fn_inst_wf fn ==> fn_inst_wf fn'
Proof
  rewrite_tac[fn_inst_wf_compute] >>
  Cases_on `fn_entry_label fn`
  >- (simp[make_ssa_current_fn_def] >> strip_tac >> gvs[]) >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  irule simplify_current_phis_if_wf >>
  drule (CONJUNCT1 rename_current_blocks_wf) >> disch_then irule >>
  drule add_phi_nodes_supply_wf >> disch_then irule >> simp[]
QED
