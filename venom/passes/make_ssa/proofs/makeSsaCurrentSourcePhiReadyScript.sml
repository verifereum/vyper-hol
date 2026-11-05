Theory makeSsaCurrentSourcePhiReady
Ancestors makeSsaCurrentActualAvailable makeSsaCurrentAvailability makeSsaCurrentSourcePhiRuntime
  makeSsaCurrentRetainedValue makeSsaCurrentInsertedValue makeSsaCurrentPhiBatch o1PassContract
  venomWf venomExecSemantics venomExecProps venomState venomInst list

(* Source readiness is established from the completed predecessor, independently
   of any target batch or origin-agreement invariant.  Selection is first-match;
   predecessor labels in a PHI need not be unique. *)
Theorem current_actual_source_phi_selected:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phis_cover_preds fn /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  MEM phi (collect_phis hb.bb_instructions) ==>
  ?v value. MEM (p,v) (phi_pairs phi.inst_operands) /\
    resolve_phi p phi.inst_operands = SOME (Var v) /\
    lookup_var v after = SOME value
Proof
  strip_tac >>
  `MEM hb fn.fn_blocks /\ hb.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM phi hb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf phi` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `phi_well_formed phi.inst_operands` by gvs[inst_wf_def] >>
  `?v. MEM (p,v) (phi_pairs phi.inst_operands)` by
    (fs[fn_phis_cover_preds_def] >> metis_tac[]) >>
  `?src. MEM (p,src) (phi_pairs phi.inst_operands) /\
    resolve_phi p phi.inst_operands = SOME (Var src)` by
    metis_tac[current_wf_phi_resolution] >>
  `MEM h (bb_succs pb)` by
    (gvs[fn_cfg_edge_def] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def,
       optionTheory.SOME_11]) >>
  `current_available fn src p (LENGTH pb.bb_instructions)` by
    (irule current_available_edge >> metis_tac[]) >>
  `?value. lookup_var src after = SOME value` by
    (irule current_actual_predecessor_exit_available >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_actual_source_phi_ready:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phis_cover_preds fn /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  MEM phi (collect_phis hb.bb_instructions) /\
  incoming.vs_prev_bb = SOME p /\ incoming.vs_vars = after.vs_vars ==>
  IS_SOME (eval_one_phi incoming phi)
Proof
  strip_tac >> drule_all current_actual_source_phi_selected >> strip_tac >>
  `MEM hb fn.fn_blocks /\ MEM phi hb.bb_instructions` by
    metis_tac[lookup_block_MEM, livenessTransferProofsTheory.collect_phis_mem] >>
  `phi.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `LENGTH phi.inst_outputs = 1` by
    (fs[fn_inst_wf_def, EVERY_MEM] >>
     `inst_wf phi` by metis_tac[] >> gvs[inst_wf_def]) >>
  Cases_on `phi.inst_outputs` >> gvs[] >>
  simp[eval_one_phi_def, eval_operand_def, lookup_var_def] >>
  fs[lookup_var_def]
QED

Theorem current_actual_source_phi_batch:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phis_cover_preds fn /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  incoming.vs_prev_bb = SOME p /\ incoming.vs_vars = after.vs_vars ==>
  eval_phis incoming hb.bb_instructions =
    OK (FOLDR (\(out,value) t. update_var out value t) incoming
      (MAP (THE o eval_one_phi incoming) (collect_phis hb.bb_instructions)))
Proof
  strip_tac >>
  `EVERY IS_SOME
    (MAP (eval_one_phi incoming) (collect_phis hb.bb_instructions))` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule current_actual_source_phi_ready >> metis_tac[]) >>
  qspec_then `hb.bb_instructions` strip_assume_tac current_collect_phi_split >>
  metis_tac[current_eval_phis_batch]
QED

Theorem current_actual_source_phi_batch_exists:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phis_cover_preds fn /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\
  get_instruction pb before.vs_inst_idx = SOME inst /\ inst_wf inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block h fn.fn_blocks = SOME hb /\ fn_cfg_edge fn p h /\
  incoming.vs_prev_bb = SOME p /\ incoming.vs_vars = after.vs_vars ==>
  ?post. eval_phis incoming hb.bb_instructions = OK post
Proof
  metis_tac[current_actual_source_phi_batch]
QED

Theorem current_entry_source_phi_batch:
  first_block_no_phi fn /\ entry_block fn = SOME eb ==>
  eval_phis incoming eb.bb_instructions = OK incoming
Proof
  simp[first_block_no_phi_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `eb.bb_instructions` >> gvs[eval_phis_def]
QED
