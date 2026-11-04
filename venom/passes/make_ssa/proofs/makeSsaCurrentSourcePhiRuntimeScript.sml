Theory makeSsaCurrentSourcePhiRuntime
Ancestors
  makeSsaCurrentDefined makeSsaCurrentPhiRuntime makeSsaCurrentPhiBatch
  venomWf venomInst venomExecSemantics venomState stateFrame alist finite_map list

Theorem current_wf_phi_resolution:
  !ops p. phi_well_formed ops /\ (?v. MEM (p,v) (phi_pairs ops)) ==>
  ?v. MEM (p,v) (phi_pairs ops) /\ resolve_phi p ops = SOME (Var v)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def, resolve_phi_def] >>
  rpt strip_tac >> Cases_on `lbl = p` >> gvs[] >> metis_tac[]
QED

Theorem current_source_phi_edge_defined:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label ==>
  ?v. MEM (bb.bb_label,v) (phi_pairs phi.inst_operands) /\
    resolve_phi bb.bb_label phi.inst_operands = SOME (Var v) /\
    v IN FDOM out.vs_vars
Proof
  rpt strip_tac >>
  `phi_well_formed phi.inst_operands` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >>
     `inst_wf phi` by metis_tac[] >> gvs[inst_wf_def]) >>
  `?w. MEM (bb.bb_label,w) (phi_pairs phi.inst_operands)` by
    (gvs[fn_phis_cover_preds_def] >> metis_tac[]) >>
  `?v. MEM (bb.bb_label,v) (phi_pairs phi.inst_operands) /\
       resolve_phi bb.bb_label phi.inst_operands = SOME (Var v)` by
    metis_tac[current_wf_phi_resolution] >>
  qexists_tac `v` >> simp[] >>
  irule current_phi_edge_endpoint_binding >> metis_tac[]
QED

Theorem current_source_phi_edge_success:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label /\ incoming.vs_prev_bb = SOME bb.bb_label /\
  incoming.vs_vars = out.vs_vars ==>
  IS_SOME (eval_one_phi incoming phi)
Proof
  rpt strip_tac >>
  `?v. MEM (bb.bb_label,v) (phi_pairs phi.inst_operands) /\
    resolve_phi bb.bb_label phi.inst_operands = SOME (Var v) /\
    v IN FDOM out.vs_vars` by metis_tac[current_source_phi_edge_defined] >>
  `LENGTH phi.inst_outputs = 1` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >>
     `inst_wf phi` by metis_tac[] >> gvs[inst_wf_def]) >>
  `?name. phi.inst_outputs = [name]` by
    (Cases_on `phi.inst_outputs` >> gvs[] >>
     rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]) >>
  `?value. FLOOKUP out.vs_vars v = SOME value` by
    metis_tac[flookup_thm] >>
  simp[eval_one_phi_def, eval_operand_def, lookup_var_def]
QED

Theorem current_source_phi_prefix_success:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\ MEM succ fn.fn_blocks /\
  fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label /\ incoming.vs_prev_bb = SOME bb.bb_label /\
  incoming.vs_vars = out.vs_vars /\ succ.bb_instructions = prefix ++ suffix /\
  EVERY (\i. i.inst_opcode = PHI) prefix ==>
  EVERY IS_SOME (MAP (eval_one_phi incoming) prefix)
Proof
  rpt strip_tac >> simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  `x.inst_opcode = PHI` by gvs[EVERY_MEM] >>
  `MEM x succ.bb_instructions` by simp[] >>
  metis_tac[current_source_phi_edge_success]
QED

Theorem current_source_phi_prefix_exact:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\ MEM succ fn.fn_blocks /\
  fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label /\ incoming.vs_prev_bb = SOME bb.bb_label /\
  incoming.vs_vars = out.vs_vars /\ succ.bb_instructions = prefix ++ suffix /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) ==>
  eval_phis incoming succ.bb_instructions =
    OK (FOLDR (\(out,value) t. update_var out value t) incoming
      (MAP (THE o eval_one_phi incoming) prefix))
Proof
  rpt strip_tac >>
  `EVERY IS_SOME (MAP (eval_one_phi incoming) prefix)` by
    metis_tac[current_source_phi_prefix_success] >>
  metis_tac[current_eval_phis_batch]
QED

Theorem current_source_phi_prefix_exists:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phis_cover_preds fn /\ MEM succ fn.fn_blocks /\
  fn_cfg_edge fn bb.bb_label succ.bb_label /\
  current_completed_blocks fn ctx path st out /\ is_fn_path fn path /\
  path <> [] /\
  (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
  LAST path = bb.bb_label /\ incoming.vs_prev_bb = SOME bb.bb_label /\
  incoming.vs_vars = out.vs_vars /\ succ.bb_instructions = prefix ++ suffix /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) ==>
  ?post. eval_phis incoming succ.bb_instructions = OK post
Proof
  metis_tac[current_source_phi_prefix_exact]
QED

Theorem current_source_phi_prefix_lookup:
  succ.bb_instructions = prefix ++ suffix /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  eval_phis incoming succ.bb_instructions = OK post ==>
  lookup_var v post =
    case alist$ALOOKUP (MAP (THE o eval_one_phi incoming) prefix) v of
      NONE => lookup_var v incoming | SOME value => SOME value
Proof
  metis_tac[current_eval_phis_batch_lookup]
QED

Theorem current_source_phi_prefix_frame:
  succ.bb_instructions = prefix ++ suffix /\
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  eval_phis incoming succ.bb_instructions = OK post ==>
  execution_frame post = execution_frame incoming
Proof
  metis_tac[current_eval_phis_batch_frame]
QED
