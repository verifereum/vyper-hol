Theory loadElimStaticPhiClosure
Ancestors
  loadElimStaticPhiInputs loadElimStaticPhiPlacement loadElimRoundStructure
  loadElimCoupledExecution cfgAnalysisProps loadElimPhiCapture codegenReadyCompute
  loadElimRoundWf loadElimRoundUniqueness loadElimDefs loadElimOriginHelpers
  loadElimKeyShapeInvariant analysisSimDefs passSimulationDefs passSimulationProps
  venomWf venomInst cfgDefs list pred_set

Theorem le_round_cfg_edge:
  le_configured_context ctx ==>
  (fn_cfg_edge (load_elim_one ctx g fn) a b <=> fn_cfg_edge fn a b)
Proof
  strip_tac >>
  simp[fn_cfg_edge_def, load_elim_one_def,
    analysis_function_transform_prepend_def, function_map_transform_def,
    MEM_MAP] >>
  eq_tac >> strip_tac >> gvs[]
  >- (qexists `y` >> gvs[le_prepend_bb_succs,
        analysis_block_transform_prepend_def]) >>
  qexists `analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend (collect_phi_actions (fn_max_inst_id fn) ctx g
      (load_analyze ctx fn) fn)) (\ll inst. [load_elim_inst ctx
      (collect_phi_actions (fn_max_inst_id fn) ctx g (load_analyze ctx fn) fn)
      ll inst]) bb` >>
  simp[le_prepend_bb_succs] >>
  simp[analysis_block_transform_prepend_def] >> metis_tac[]
QED

Theorem le_round_dominates:
  le_configured_context ctx ==>
  (fn_dominates (load_elim_one ctx g fn) d n <=> fn_dominates fn d n)
Proof
  strip_tac >>
  `!xs. is_fn_path (load_elim_one ctx g fn) xs <=> is_fn_path fn xs` by
    (Induct >> simp[is_fn_path_def] >> Cases_on `xs` >>
     simp[is_fn_path_def, le_round_cfg_edge]) >>
  `fn_cfg_edge (load_elim_one ctx g fn) = fn_cfg_edge fn` by
    simp[FUN_EQ_THM, le_round_cfg_edge] >>
  simp[fn_dominates_def, fn_reachable_def, le_round_entry]
QED

Theorem le_configured_outputs_retained:
  le_configured_context ctx /\ inst_wf i ==>
  (load_elim_inst ctx actions ll i).inst_outputs = i.inst_outputs
Proof
  strip_tac >>
  Cases_on `load_elim_inst ctx actions ll i = i` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def,
      inst_wf_def, passSharedDefsTheory.mk_assign_inst_def,
      passSharedDefsTheory.mk_nop_inst_def]
QED

Theorem le_prepend_definition_retained:
  le_configured_context ctx /\ EVERY inst_wf bb.bb_instructions /\
  MEM i bb.bb_instructions /\ MEM v i.inst_outputs ==>
  ?j. MEM j (analysis_block_transform_prepend NONE result
      (load_phi_prepend actions) (\ll inst. [load_elim_inst ctx actions ll inst])
      bb).bb_instructions /\ MEM v j.inst_outputs
Proof
  strip_tac >>
  `?n. n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = i` by
    metis_tac[MEM_EL] >>
  qexists `load_elim_inst ctx actions (df_at NONE result bb.bb_label n) i` >>
  reverse conj_tac
  >- metis_tac[le_configured_outputs_retained, EVERY_MEM] >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
    flat_mapi_singleton, MEM_APPEND] >>
  `MEM (load_elim_inst ctx actions (df_at NONE result bb.bb_label n) i)
    (MAPi (\idx inst. load_elim_inst ctx actions
      (df_at NONE result bb.bb_label idx) inst) bb.bb_instructions)` by
    (simp[indexedListsTheory.MEM_MAPi] >> qexists `n` >> simp[]) >>
  metis_tac[TAKE_DROP, MEM_APPEND]
QED

Theorem le_round_endpoint_available:
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  MEM pb fn.fn_blocks /\ def_available_at fn pb NONE v ==>
  ?pb'. MEM pb' (load_elim_one ctx (cfg_analyze fn) fn).fn_blocks /\
    pb'.bb_label = pb.bb_label /\
    def_available_at (load_elim_one ctx (cfg_analyze fn) fn) pb' NONE v
Proof
  strip_tac >>
  qabbrev_tac `transformed = load_elim_one ctx (cfg_analyze fn) fn` >>
  qabbrev_tac `actions = collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn` >>
  qabbrev_tac `tr = analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend actions) (\ll inst. [load_elim_inst ctx actions ll inst])` >>
  qexists `tr pb` >>
  `!bb. (tr bb).bb_label = bb.bb_label` by
    simp[Abbr `tr`, analysis_block_transform_prepend_def] >>
  `transformed.fn_blocks = MAP tr fn.fn_blocks` by
    simp[Abbr `transformed`, Abbr `tr`, Abbr `actions`, load_elim_one_def,
      analysis_function_transform_prepend_def, function_map_transform_def] >>
  simp[MEM_MAP] >>
  conj_tac >- metis_tac[] >>
  fs[def_available_at_def] >>
  `EVERY inst_wf def_bb.bb_instructions` by
    metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  drule_all le_prepend_definition_retained >>
  disch_then (qspecl_then [`load_analyze ctx fn`, `actions`] strip_assume_tac) >>
  qexistsl [`tr def_bb`, `j`] >>
  simp[MEM_MAP] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[Abbr `tr`] >>
  simp[Abbr `transformed`, le_round_dominates]
QED

Theorem le_generated_phi_edge_uses_wf:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\ le_configured_context ctx /\
  MEM phi (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn) tb.bb_label) ==>
  phi_edge_uses_wf (load_elim_one ctx (cfg_analyze fn) fn) tb phi
Proof
  strip_tac >> drule phis_for_block_member >> strip_tac >> gvs[] >>
  drule collect_phi_actions_member >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  simp[phi_edge_uses_wf_def, le_phi_ops_well_formed, le_phi_pairs_generated,
    le_cfg_preds_distinct, le_round_cfg_edge] >>
  conj_tac
  >- (gen_tac >>
      `MEM pred (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) <=>
       ?p. MEM p pairs /\ FST p = pred` by
        (qpat_x_assum `MAP FST pairs = _` (fn th => rewrite_tac[GSYM th]) >>
         simp[MEM_MAP] >> metis_tac[]) >>
      metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond]) >>
  rpt strip_tac >>
  `MEM (pred,v) (phi_pairs pa.pa_phi_ops)` by simp[le_phi_pairs_generated] >>
  drule_all le_collected_phi_input_available >> strip_tac >>
  drule_all le_round_endpoint_available >> strip_tac >>
  metis_tac[]
QED
