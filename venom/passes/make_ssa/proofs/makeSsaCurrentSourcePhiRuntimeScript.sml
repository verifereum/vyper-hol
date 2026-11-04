Theory makeSsaCurrentSourcePhiRuntime
Ancestors
  makeSsaCurrentDefined makeSsaCurrentPhiRuntime makeSsaCurrentPhiBatch
  venomWf venomInst venomExecSemantics venomState finite_map list

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
