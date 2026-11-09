Theory loadElimRoundUniqueness
Ancestors
  loadElimRoundWf loadElimListInsertion loadElimTargetWrites
  loadElimDefs loadElimOriginHelpers loadElimActionFreshness
  venomWf venomInst passSharedDefs irSupply indexedLists list rich_list pred_set
  analysisSimDefs passSimulationDefs passSimulationProps cfgTransform

Theorem le_collected_action_id_sublist:
  sublist (MAP (\pa. pa.pa_phi_id) (collect_phi_actions m ctx cfg result fn))
    (FLAT (MAP (\bb. MAP (\inst. fresh_phi_id m inst.inst_id)
                            bb.bb_instructions) fn.fn_blocks))
Proof
  pure_rewrite_tac[collect_phi_actions_def, LET_THM] >>
  BETA_TAC >> ho_match_mp_tac le_optional_blocks_output_sublist >>
  rpt gen_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  drule compute_phi_action_origin >> simp[]
QED

Theorem le_collected_action_ids_distinct:
  wf_function fn ==>
  ALL_DISTINCT (MAP (\pa. pa.pa_phi_id) (collect_phi_actions m ctx cfg result fn))
Proof
  strip_tac >> irule sublist_ALL_DISTINCT >>
  irule_at Any le_collected_action_id_sublist >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
                                    bb.bb_instructions) fn.fn_blocks))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  `ALL_DISTINCT (MAP (fresh_phi_id m)
     (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)))` by
    (irule ALL_DISTINCT_MAP_INJ >> simp[fresh_phi_id_def]) >>
  fs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem le_source_inst_id_bound:
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions ==>
  i.inst_id <= fn_max_inst_id fn
Proof
  strip_tac >> simp[fn_max_inst_id_def] >>
  irule foldl_max_bound >> simp[MEM_MAP, MEM_FLAT] >> metis_tac[]
QED

Theorem le_collected_action_id_bound:
  MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ==>
  fn_max_inst_id fn < pa.pa_phi_id
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule compute_phi_action_origin >> simp[fresh_phi_id_def]
QED

Theorem le_inst_id_preserved:
  (load_elim_inst ctx actions ll i).inst_id = i.inst_id
Proof
  Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_inst_outputs_preserved_or_empty:
  (load_elim_inst ctx actions ll i).inst_outputs = i.inst_outputs \/
  (load_elim_inst ctx actions ll i).inst_outputs = []
Proof
  Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_mapi_ids:
  !xs f. MAP (\i. i.inst_id)
    (MAPi (\n i. load_elim_inst ctx actions (f n) i) xs) =
    MAP (\i. i.inst_id) xs
Proof
  Induct >> simp[indexedListsTheory.MAPi_def, le_inst_id_preserved,
                 combinTheory.o_DEF] >> metis_tac[]
QED

Theorem le_mapi_outputs_sublist:
  !xs f. sublist
    (FLAT (MAP (\i. i.inst_outputs)
      (MAPi (\n i. load_elim_inst ctx actions (f n) i) xs)))
    (FLAT (MAP (\i. i.inst_outputs) xs))
Proof
  Induct >- simp[sublist_def] >> rpt gen_tac >>
  pure_rewrite_tac[indexedListsTheory.MAPi_def, combinTheory.o_DEF, MAP, FLAT] >>
  irule sublist_append_pair >> conj_tac
  >- (Cases_on `(load_elim_inst ctx actions (f 0) h).inst_outputs = []` >>
      simp[sublist_def] >> metis_tac[le_inst_outputs_preserved_or_empty, sublist_refl]) >>
  first_x_assum (qspec_then `f o SUC` mp_tac) >> simp[combinTheory.o_DEF]
QED

Theorem le_retained_outputs_sublist:
  !bs f. sublist
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
      (MAPi (\n i. load_elim_inst ctx actions (f bb n) i) bb.bb_instructions))) bs))
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bs))
Proof
  Induct >- simp[sublist_def] >> rpt gen_tac >>
  pure_rewrite_tac[MAP, FLAT] >> BETA_TAC >>
  irule sublist_append_pair >> simp[le_mapi_outputs_sublist]
QED

Theorem le_routed_phi_ids:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bs) /\
  ALL_DISTINCT (MAP (\pa. pa.pa_phi_id) actions) ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
    (phis_for_block actions bb.bb_label)) bs))
Proof
  simp[phis_for_block_def, MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
  mp_tac le_filtered_routing_distinct >>
  disch_then (mp_tac o Q.ISPECL [`MAP (\bb:basic_block. bb.bb_label) bs`, `actions : phi_action list`,
    `\pa. pa.pa_phi_id`, `\pa. pa.pa_join_lbl`]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem le_routed_phi_outputs:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bs) /\
  ALL_DISTINCT (MAP (\pa. pa.pa_phi_out) actions) ==>
  ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
    (phis_for_block actions bb.bb_label))) bs))
Proof
  `!xs : phi_action list. FLAT (MAP (\pa. [pa.pa_phi_out]) xs) =
    MAP (\pa. pa.pa_phi_out) xs` by (Induct >> simp[]) >>
  simp[phis_for_block_def, MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
  mp_tac le_filtered_routing_distinct >>
  disch_then (mp_tac o Q.ISPECL [`MAP (\bb:basic_block. bb.bb_label) bs`, `actions : phi_action list`,
    `\pa. pa.pa_phi_out`, `\pa. pa.pa_join_lbl`]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem le_round_inst_ids_distinct:
  wf_function fn ==> fn_inst_ids_distinct (load_elim_one ctx g fn)
Proof
  strip_tac >>
  simp[load_elim_one_def, analysis_function_transform_prepend_def,
       function_map_transform_def, fn_inst_ids_distinct_def,
       analysis_block_transform_prepend_def, load_phi_prepend_def,
       flat_mapi_singleton, MAP_MAP_o, combinTheory.o_DEF,
       MAP_APPEND, MAP_TAKE, MAP_DROP, Excl "MAP_MAPi"] >>
  ho_match_mp_tac le_flat_insert_distinct >>
  conj_tac
  >- (simp[le_mapi_ids] >> gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  conj_tac
  >- (irule le_routed_phi_ids >>
      simp[le_collected_action_ids_distinct] >> gvs[wf_function_def, fn_labels_def]) >>
  simp[le_mapi_ids] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  drule phis_for_block_member >> strip_tac >> gvs[] >>
  drule le_collected_action_id_bound >> strip_tac >>
  drule_all le_source_inst_id_bound >> simp[]
QED

Theorem le_round_preserves_wf_function:
  le_configured_context ctx /\ wf_function fn ==>
  wf_function (load_elim_one ctx g fn)
Proof
  metis_tac[le_round_wf_from_ids, le_round_inst_ids_distinct]
QED

Theorem le_round_preserves_ssa_form:
  wf_function fn /\ ssa_form fn /\
  (!pa i. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx g
                    (load_analyze ctx fn) fn) /\ MEM i (fn_insts fn) ==>
          ~MEM pa.pa_phi_out i.inst_outputs) ==>
  ssa_form (load_elim_one ctx g fn)
Proof
  strip_tac >>
  `!bs. fn_insts_blocks bs = FLAT (MAP (\bb. bb.bb_instructions) bs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  simp[load_elim_one_def, analysis_function_transform_prepend_def,
       function_map_transform_def, ssa_form_def, fn_insts_def,
       analysis_block_transform_prepend_def, load_phi_prepend_def,
       flat_mapi_singleton, MAP_MAP_o, combinTheory.o_DEF,
       MAP_FLAT, FLAT_FLAT, Excl "MAP_MAPi", Excl "MAP_APPEND", Excl "FLAT_APPEND"] >>
  ho_match_mp_tac le_flat_insert_projection_distinct >>
  conj_tac
  >- (irule sublist_ALL_DISTINCT >>
      qexists_tac `FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
        bb.bb_instructions)) fn.fn_blocks)` >> conj_tac
      >- gvs[ssa_form_def, fn_insts_def, MAP_FLAT, FLAT_FLAT,
             MAP_MAP_o, combinTheory.o_DEF] >>
      simp[le_retained_outputs_sublist]) >>
  conj_tac
  >- (irule le_routed_phi_outputs >>
      simp[le_collected_action_outputs_distinct] >>
      gvs[wf_function_def, fn_labels_def]) >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  drule phis_for_block_member >> strip_tac >> gvs[] >>
  gvs[MEM_MAPi, combinTheory.o_DEF, fn_insts_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL, le_inst_outputs_preserved_or_empty, MEM]
QED

Theorem le_round_preserves_ssa_form_prefix:
  wf_function fn /\ ssa_form fn /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  ssa_form (load_elim_one ctx g fn)
Proof
  strip_tac >> irule le_round_preserves_ssa_form >> simp[] >>
  rpt strip_tac >>
  `~MEM pa.pa_phi_out (fn_all_vars fn)` by
    metis_tac[le_collected_action_source_disjoint] >>
  `!bs. fn_insts_blocks bs = FLAT (MAP (\bb. bb.bb_instructions) bs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  gvs[fn_insts_def, MEM_FLAT, MEM_MAP] >>
  `MEM pa.pa_phi_out (fn_all_vars fn)` by
    (simp[NoAsms, fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND, PULL_EXISTS] >>
     qexists_tac `bb` >> simp[MEM_FLAT, MEM_MAP, MEM_APPEND, PULL_EXISTS] >>
     qexists_tac `i` >> simp[]) >>
  metis_tac[]
QED
