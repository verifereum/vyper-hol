Theory loadElimStaticPhiClosure
Ancestors
  loadElimStaticPhiInputs loadElimStaticPhiPlacement loadElimRoundStructure
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
