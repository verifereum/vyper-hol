Theory loadElimRoundWf
Ancestors
  loadElimDefs loadElimOriginHelpers loadElimPhiCapture loadElimActionFreshness
  loadElimRoundStructure venomWf passSharedDefs list rich_list

Theorem le_phi_ops_well_formed:
  !pairs. phi_well_formed (mk_phi_ops_from_pairs pairs)
Proof
  Induct >> simp[mk_phi_ops_from_pairs_def, phi_well_formed_def] >>
  Cases_on `h` >> simp[mk_phi_ops_from_pairs_def, phi_well_formed_def]
QED

Theorem le_computed_phi_inst_wf:
  compute_phi_action m g r k lbl i = SOME pa ==>
  inst_wf <| inst_id := pa.pa_phi_id; inst_opcode := PHI;
    inst_operands := pa.pa_phi_ops; inst_outputs := [pa.pa_phi_out] |>
Proof
  strip_tac >> drule le_compute_phi_action_certificate >> strip_tac >>
  simp[inst_wf_def, le_phi_ops_well_formed]
QED

Theorem le_collected_phi_inst_wf:
  MEM pa (collect_phi_actions m ctx g r fn) ==>
  inst_wf <| inst_id := pa.pa_phi_id; inst_opcode := PHI;
    inst_operands := pa.pa_phi_ops; inst_outputs := [pa.pa_phi_out] |>
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  metis_tac[le_computed_phi_inst_wf]
QED

Theorem le_phis_for_block_inst_wf:
  EVERY inst_wf (phis_for_block (collect_phi_actions m ctx g r fn) lbl)
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule phis_for_block_member >> strip_tac >>
  metis_tac[le_collected_phi_inst_wf]
QED

Theorem le_inst_preserves_inst_wf:
  inst_wf i ==> inst_wf (load_elim_inst ctx actions ll i)
Proof
  strip_tac >>
  Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[inst_wf_def, mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_round_preserves_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (load_elim_one ctx g fn)
Proof
  simp[fn_inst_wf_def, load_elim_one_def,
       analysisSimDefsTheory.analysis_function_transform_prepend_def,
       passSimulationDefsTheory.function_map_transform_def] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  `EVERY inst_wf bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `EVERY inst_wf
    (MAPi (\n i. load_elim_inst ctx
      (collect_phi_actions (fn_max_inst_id fn) ctx g (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) bb.bb_label n) i) bb.bb_instructions)` by
    (gvs[EVERY_EL, indexedListsTheory.LENGTH_MAPi, indexedListsTheory.EL_MAPi] >>
     metis_tac[le_inst_preserves_inst_wf]) >>
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[analysisSimDefsTheory.analysis_block_transform_prepend_def,
       load_phi_prepend_def, passSimulationPropsTheory.flat_mapi_singleton, MEM_APPEND] >>
  metis_tac[le_phis_for_block_inst_wf, EVERY_MEM, EVERY_TAKE, EVERY_DROP]
QED
