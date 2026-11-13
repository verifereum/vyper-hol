(* Generated collapse maps only name removed blocks.  Normalized functions
   have no references to those labels in positions rewritten by substitution. *)
Theory simplifyCfgGeneratedSubst
Ancestors
  simplifyCfgShapeCore
  simplifyCfgStaticInterface simplifyCfgLabelProps simplifyCfgBypassShape
  cfgTransform venomWf venomInst unitShapeDefs stackPlanTypes list rich_list
  unitLabelMapIdentity
  simplifyCfgStruct

Theorem scfg_term_label_successor:
  is_terminator i.inst_opcode /\ scfg_label_positions i /\
  MEM (Label l) i.inst_operands ==> MEM l (get_successors i)
Proof
  strip_tac >> Cases_on `i.inst_opcode = JMP`
  >- (drule scfg_jmp_label_positions >> simp[] >> strip_tac
      >- (fs[EVERY_MEM] >> first_x_assum (qspec_then `Label l` mp_tac) >>
          simp[is_label_operand_def]) >>
      gvs[get_successors_def, venomStateTheory.get_label_def]) >>
  Cases_on `i.inst_opcode = JNZ`
  >- (drule scfg_jnz_label_positions >> simp[] >> strip_tac
      >- (fs[EVERY_MEM] >> first_x_assum (qspec_then `Label l` mp_tac) >>
          simp[is_label_operand_def]) >>
      gvs[get_successors_def, venomStateTheory.get_label_def] >> Cases_on `c` >> gvs[is_label_operand_def, venomStateTheory.get_label_def]) >>
  drule_all scfg_other_term_nonlabels >> simp[EVERY_MEM] >>
  metis_tac[is_label_operand_def]
QED

Theorem scfg_normalized_rewritten_label:
  scfg_normalized fn /\ MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  is_block_label_opcode i.inst_opcode /\ MEM (Label l) i.inst_operands ==>
  MEM l (fn_labels fn)
Proof
  strip_tac >> Cases_on `i.inst_opcode = PHI`
  >- (`MEM l (pred_labels fn bb.bb_label)` by
        metis_tac[scfg_normalized_def] >>
      fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_labels_def] >>
      metis_tac[]) >>
  `wf_function fn /\ scfg_shape fn` by
    metis_tac[scfg_normalized_static, scfg_static_wf, scfg_static_shape] >>
  `is_terminator i.inst_opcode` by fs[is_block_label_opcode_def] >>
  `scfg_label_positions i` by
    (fs[scfg_shape_def, EVERY_MEM, scfg_inst_shape_def] >> metis_tac[fn_insts_MEM]) >>
  `MEM l (get_successors i)` by metis_tac[scfg_term_label_successor] >>
  `i = LAST bb.bb_instructions /\ bb.bb_instructions <> []` by
    metis_tac[bb_well_formed_terminator_last, wf_function_def, bb_well_formed_def] >>
  `MEM l (bb_succs bb)` by (Cases_on `bb.bb_instructions` >> gvs[bb_succs_def]) >>
  metis_tac[wf_function_def, fn_succs_closed_def]
QED

Theorem scfg_subst_block_labels_invoke[simp]:
  i.inst_opcode = INVOKE ==> subst_block_labels_inst lm i = i
Proof
  simp[subst_block_labels_inst_def, is_block_label_opcode_def, is_terminator_def]
QED

Theorem scfg_normalized_subst_identity:
  scfg_normalized fn /\
  (!l. MEM l (fn_labels fn) ==> ~MEM l (MAP FST lm)) ==>
  subst_block_labels_fn lm fn = fn
Proof
  strip_tac >> simp[subst_block_labels_fn_def] >>
  `MAP (subst_block_labels_block lm) fn.fn_blocks = fn.fn_blocks` suffices_by simp[] >>
  irule MAP_eq_self >> rpt strip_tac >>
  simp[subst_block_labels_block_def] >>
  `MAP (subst_block_labels_inst lm) x.bb_instructions = x.bb_instructions`
    suffices_by simp[] >>
  irule MAP_eq_self >> rpt strip_tac >> simp[subst_block_labels_inst_def] >>
  IF_CASES_TAC >> simp[] >> irule subst_label_map_inst_id >> rpt strip_tac >>
  metis_tac[scfg_normalized_rewritten_label]
QED

Theorem scfg_generated_subst_identity:
  scfg_normalized fn /\ label_map_transition initial lm (fn_labels fn) ==>
  subst_block_labels_fn lm fn = fn
Proof
  strip_tac >> irule scfg_normalized_subst_identity >> simp[] >>
  fs[label_map_transition_def, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_event_subst_identity:
  scfg_normalized fn /\ fn_result_events initial [] fn lm ==>
  subst_block_labels_fn lm fn = fn
Proof
  strip_tac >> irule scfg_normalized_subst_identity >> simp[] >>
  fs[fn_result_events_def] >> drule label_event_trace_sources_absent >>
  simp[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem scfg_collapse_subst_identity:
  ALL_DISTINCT (fn_labels fn) /\
  collapse_dfs fn [] visited lbl = (fn',lm,visited') /\ scfg_normalized fn' ==>
  subst_block_labels_fn lm fn' = fn'
Proof
  strip_tac >> irule scfg_event_subst_identity >> simp[] >>
  `collapse_dfs_result (collapse_result_events (fn_labels fn) []) fn [] visited lbl` by
    metis_tac[collapse_events_joint] >>
  fs[collapse_dfs_result_def, collapse_result_events_def] >> gvs[] >> metis_tac[]
QED
