(*
 * MakeSSA's output meets what MakeSSA needs of its input
 * (make_ssa_input_ok), but for non-degeneracy, which
 * makeSsaCurrentNonDegenerate gives: the first O1 run's output is the
 * second run's input, up to the three passes between them.  The pass
 * keeps the blocks and the CFG, so every block stays reachable; its
 * output is SSA (makeSsaCurrentWfSsa), so every variable is written once
 * and definitions reach their uses; each PHI it places has one pair per
 * predecessor, and renaming keeps the pairs of the PHIs it is given.
 *)
Theory makeSsaCurrentInputOk
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract makeSsaCurrentProps makeSsaCurrentWfSsa makeSsaCurrentCfg

Theorem make_ssa_current_fn_input_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  all_reachable fn' /\ fn_defs_reach_uses fn' /\
  fn_phi_operands_single_def fn' /\ fn_phis_cover_preds fn' /\
  fn_phi_outputs_single_def fn' /\
  (!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn' l bb.bb_label)
Proof
  strip_tac >>
  `wf_ssa fn'` by
    (drule_at (Pos last) make_ssa_current_fn_wf_ssa >>
     gvs[make_ssa_input_ok_def] >> disch_then irule >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `ALL_DISTINCT (fn_labels fn')` by
    (drule make_ssa_current_fn_labels >> fs[fn_labels_def]) >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  drule_all make_ssa_current_fn_all_reachable >> strip_tac >>
  drule_all wf_ssa_defs_reach_uses_distinct >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn')))` by
    fs[wf_ssa_def, ssa_form_def] >>
  `!bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==> phi_edge_uses_wf fn' bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  simp[fn_phi_operands_single_def_def, fn_phi_outputs_single_def_def,
       ssa_outputs_single_def] >>
  simp[fn_phis_cover_preds_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[phi_edge_uses_wf_def] >> strip_tac
  >- (qpat_x_assum `!pred. _ <=> _` (qspec_then `pred` mp_tac) >>
      simp[pairTheory.EXISTS_PROD])
  >> metis_tac[]
QED
