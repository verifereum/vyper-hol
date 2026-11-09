Theory loadElimRoundWf
Ancestors
  loadElimDefs loadElimOriginHelpers loadElimPhiCapture loadElimActionFreshness
  loadElimRoundStructure venomWf venomInst venomExecSemantics passSharedDefs list rich_list

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

Theorem le_configured_terminator_classification:
  le_configured_context ctx ==>
  (is_terminator (load_elim_inst ctx actions ll i).inst_opcode <=>
   is_terminator i.inst_opcode)
Proof
  strip_tac >>
  Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[loadElimKeyShapeInvariantTheory.le_configured_context_def,
      memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def,
      mk_assign_inst_def, mk_nop_inst_def, is_terminator_def]
QED

Theorem le_mapi_bb_well_formed:
  le_configured_context ctx /\ bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAPi (\n i. load_elim_inst ctx actions (lats n) i) bb.bb_instructions)
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `MAPi (\n i. load_elim_inst ctx actions (lats n) i) bb.bb_instructions <> []` by
    (strip_tac >>
     qpat_x_assum `MAPi _ _ = []` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[indexedListsTheory.LENGTH_MAPi]) >>
  gvs[bb_well_formed_def, LAST_EL, indexedListsTheory.LENGTH_MAPi,
      indexedListsTheory.EL_MAPi, le_configured_terminator_classification,
      loadElimTargetWritesTheory.le_configured_phi_classification] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  conj_tac >- simp[indexedListsTheory.EL_MAPi, le_configured_terminator_classification] >>
  conj_tac >> rpt strip_tac >>
  gvs[indexedListsTheory.EL_MAPi, le_configured_terminator_classification,
      loadElimTargetWritesTheory.le_configured_phi_classification] >>
  metis_tac[]
QED

Theorem le_phi_cons_bb_well_formed:
  h.inst_opcode = PHI ==>
  (bb_well_formed (basic_block lbl (h::xs)) <=>
   bb_well_formed (basic_block lbl xs))
Proof
  strip_tac >> Cases_on `xs` >- simp[bb_well_formed_def, is_terminator_def] >>
  simp[bb_well_formed_def, LAST_CONS_cond] >>
  eq_tac
  >- (strip_tac >> simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!i j. _` (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `i` >> gvs[is_terminator_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `i` >- simp[] >>
  Cases_on `j` >> gvs[] >> metis_tac[]
QED

Theorem le_phi_list_prepend_bb_well_formed:
  !ys xs. EVERY (\i. i.inst_opcode = PHI) ys /\
    bb_well_formed (basic_block lbl xs) ==>
    bb_well_formed (basic_block lbl (ys ++ xs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[le_phi_cons_bb_well_formed] >> metis_tac[]
QED

Theorem le_insert_phis_bb_well_formed:
  !xs ys. EVERY (\i. i.inst_opcode = PHI) ys /\
    bb_well_formed (basic_block lbl xs) ==>
    bb_well_formed (basic_block lbl
      (TAKE (phi_prefix_length xs) xs ++ ys ++ DROP (phi_prefix_length xs) xs))
Proof
  Induct >- simp[bb_well_formed_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[phi_prefix_length_def, le_phi_cons_bb_well_formed]) >>
  simp[phi_prefix_length_def] >>
  irule le_phi_list_prepend_bb_well_formed >> simp[]
QED

Theorem le_prepend_bb_well_formed:
  le_configured_context ctx /\ bb_well_formed bb ==>
  bb_well_formed
    (analysisSimDefs$analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb)
Proof
  strip_tac >> drule_all le_mapi_bb_well_formed >>
  disch_then (qspecl_then [`\n. df_at NONE result bb.bb_label n`, `actions`] mp_tac) >>
  Cases_on `bb` >>
  simp[analysisSimDefsTheory.analysis_block_transform_prepend_def,
       load_phi_prepend_def, passSimulationPropsTheory.flat_mapi_singleton] >>
  simp[basic_block_fn_updates] >> strip_tac >>
  irule le_insert_phis_bb_well_formed >>
  simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER]
QED

Theorem le_round_wf_from_ids:
  le_configured_context ctx /\ wf_function fn /\
  fn_inst_ids_distinct (load_elim_one ctx g fn) ==>
  wf_function (load_elim_one ctx g fn)
Proof
  simp[load_elim_one_def, analysisSimDefsTheory.analysis_function_transform_prepend_def] >>
  strip_tac >> irule passSimulationPropsTheory.fmt_preserves_wf_function >>
  simp[analysisSimDefsTheory.analysis_block_transform_prepend_def,
       le_prepend_bb_well_formed, le_prepend_bb_succs]
QED
