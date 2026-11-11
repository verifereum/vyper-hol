Theory loadElimTargetWrites
Ancestors
  loadElimOriginHelpers loadElimActionFreshness loadElimOperationalHistory
  loadElimActualGeneration loadElimOccurrenceCoverage loadElimDefs
  passSharedDefs venomInst venomWf cfgTransform
  list rich_list pred_set

Theorem le_transformed_outputs_subset:
  set (load_elim_inst ctx actions ll inst).inst_outputs SUBSET set inst.inst_outputs
Proof
  Cases_on `load_elim_inst ctx actions ll inst = inst` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_phi_outputs_cons:
  le_phi_outputs (i::is) =
    if i.inst_opcode = PHI then set i.inst_outputs UNION le_phi_outputs is else {}
Proof
  simp[le_phi_outputs_def, le_phi_prefix_def] >> IF_CASES_TAC >> simp[]
QED

Theorem le_prepended_phi_outputs:
  !actions. le_phi_outputs (phis_for_block actions lbl ++ rest) SUBSET
    ({a.pa_phi_out | MEM a actions /\ a.pa_join_lbl = lbl} UNION le_phi_outputs rest)
Proof
  Induct >> simp[phis_for_block_def] >> rpt gen_tac >>
  Cases_on `h.pa_join_lbl = lbl`
  >- (gvs[le_phi_outputs_cons, phis_for_block_def] >>
      conj_tac >- (disj1_tac >> qexists_tac `h` >> simp[]) >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
  gvs[le_phi_outputs_cons, phis_for_block_def] >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_configured_phi_unchanged:
  le_configured_context ctx /\ inst.inst_opcode = PHI ==>
  load_elim_inst ctx actions ll inst = inst
Proof
  strip_tac >> irule load_elim_inst_unchanged >>
  gvs[loadElimKeyShapeInvariantTheory.le_configured_context_def,
      memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]
QED

Theorem le_configured_phi_classification:
  le_configured_context ctx ==>
  ((load_elim_inst ctx actions ll inst).inst_opcode = PHI <=>
   inst.inst_opcode = PHI)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- metis_tac[le_configured_phi_unchanged] >>
  Cases_on `load_elim_inst ctx actions ll inst = inst` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_configured_transformed_phi_prefix:
  !xs lats. le_configured_context ctx ==>
    le_phi_prefix (MAPi (\n i. load_elim_inst ctx actions (lats n) i) xs) =
    le_phi_prefix xs
Proof
  Induct >- simp[le_phi_prefix_def] >> rpt strip_tac >>
  simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF,
       le_phi_prefix_def, le_configured_phi_classification] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[le_configured_phi_unchanged]
QED

Theorem le_selected_output_other_join:
  ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\ MEM pa actions /\
  lbl <> pa.pa_join_lbl /\ pa.pa_phi_out NOTIN le_phi_outputs rest ==>
  pa.pa_phi_out NOTIN le_phi_outputs (phis_for_block actions lbl ++ rest)
Proof
  strip_tac >>
  qpat_x_assum `MEM pa actions` mp_tac >> simp[MEM_SPLIT] >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP] >>
  mp_tac le_prepended_phi_outputs >>
  disch_then (qspec_then `l1 ++ pa::l2` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_collected_transformed_output_fresh:
  ~MEM pa.pa_phi_out (fn_all_vars fn) /\
  MEM pa (collect_phi_actions m ctx cfg result fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  ~MEM pa.pa_phi_out (load_elim_inst ctx actions ll inst).inst_outputs
Proof
  strip_tac >>
  mp_tac le_transformed_outputs_subset >> simp[SUBSET_DEF] >>
  strip_tac >> strip_tac >>
  `MEM pa.pa_phi_out inst.inst_outputs` by metis_tac[] >>
  qpat_x_assum `~MEM _ (fn_all_vars fn)` mp_tac >>
  simp[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem le_collected_other_join_phi_fresh:
  wf_function fn /\ le_configured_context ctx /\
  ~MEM pa.pa_phi_out (fn_all_vars fn) /\
  MEM pa (collect_phi_actions m ctx cfg result fn) /\
  MEM bb fn.fn_blocks /\ bb.bb_label <> pa.pa_join_lbl ==>
  pa.pa_phi_out NOTIN le_phi_outputs
    (phis_for_block (collect_phi_actions m ctx cfg result fn) bb.bb_label ++
     MAPi (\n i. load_elim_inst ctx (collect_phi_actions m ctx cfg result fn) (lats n) i)
       bb.bb_instructions)
Proof
  strip_tac >> irule le_selected_output_other_join >>
  simp[le_collected_action_outputs_distinct] >>
  simp[le_phi_outputs_def, le_configured_transformed_phi_prefix] >>

  simp[le_phi_prefix_take, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  gen_tac >> spose_not_then strip_assume_tac >>
  drule MEM_TAKE >> strip_tac >>
  qpat_x_assum `~MEM _ (fn_all_vars fn)` mp_tac >>
  simp[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED
