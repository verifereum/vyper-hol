Theory loadElimRoundReachableSSA
Ancestors
  loadElimStaticPointClosure loadElimStaticPhiClosure loadElimRoundUniqueness
  loadElimStaticAvailability loadElimStaticPhiPlacement loadElimReachableSSA
  loadElimTargetWrites loadElimOriginHelpers loadElimDefs loadElimPrependIndex passTransform
  analysisSimDefs passSimulationDefs passSimulationProps passSharedDefs venomWf venomInst
  venomExecSemantics venomExecProofs indexedLists list rich_list finite_map
  loadElimActionSelection loadElimPhiCapture cfgAnalysisProps

Theorem le_prepend_member_cases:
  MEM j (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
    (\ll i. [load_elim_inst ctx actions ll i]) bb).bb_instructions ==>
  MEM j (phis_for_block actions bb.bb_label) \/
  ?n. n < LENGTH bb.bb_instructions /\
    j = load_elim_inst ctx actions (df_at NONE result bb.bb_label n)
      (EL n bb.bb_instructions)
Proof
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
    flat_mapi_singleton, MEM_APPEND] >> strip_tac >> simp[] >>
  `MEM j (MAPi (\n i. load_elim_inst ctx actions
      (df_at NONE result bb.bb_label n) i) bb.bb_instructions)` by
    metis_tac[TAKE_DROP, MEM_APPEND] >>
  gvs[MEM_MAPi] >> metis_tac[]
QED

Theorem le_non_phi_prefix_bound[local]:
  !xs n. n < LENGTH xs /\ (EL n xs).inst_opcode <> PHI ==>
    phi_prefix_length xs <= n
Proof
  Induct >> simp[phi_prefix_length_def] >>
  Cases_on `n` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >> gvs[]
QED

Theorem le_action_lookup_join_dominates:
  wf_function fn /\ MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  phi_action_lookup (collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn)
    (EL n bb.bb_instructions).inst_id = SOME out ==>
  ?pa. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn) /\
    pa.pa_phi_out = out /\ fn_dominates fn pa.pa_join_lbl bb.bb_label
Proof
  strip_tac >> drule_at (Pat `phi_action_lookup _ _ = _`)
    le_collected_action_at_position >>
  disch_then (qspecl_then [`n`, `bb`] mp_tac) >> simp[] >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `1 < LENGTH vs` by fs[arithmeticTheory.GREATER_DEF] >>
  drule_all le_static_multivalue_join_dominates >> strip_tac >>
  metis_tac[]
QED

Theorem le_round_mapped_ordinary_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ n < LENGTH bb.bb_instructions /\
  (EL n bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (load_elim_inst ctx
    (collect_phi_actions (fn_max_inst_id fn) ctx (cfg_analyze fn)
      (load_analyze ctx fn) fn)
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)
    (EL n bb.bb_instructions)).inst_operands ==>
  def_available_at (load_elim_one ctx (cfg_analyze fn) fn)
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll i. [load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
        (cfg_analyze fn) (load_analyze ctx fn) fn) ll i]) bb)
    (SOME (load_elim_inst ctx (collect_phi_actions (fn_max_inst_id fn) ctx
      (cfg_analyze fn) (load_analyze ctx fn) fn)
      (df_at NONE (load_analyze ctx fn) bb.bb_label n)
      (EL n bb.bb_instructions))) v
Proof
  strip_tac >>
  `phi_prefix_length bb.bb_instructions <= n` by
    metis_tac[le_non_phi_prefix_bound] >>
  qabbrev_tac `actions = collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn` >>
  qabbrev_tac `i = EL n bb.bb_instructions` >>
  qabbrev_tac `ll = df_at NONE (load_analyze ctx fn) bb.bb_label n` >>
  Cases_on `load_elim_inst ctx actions ll i = i`
  >- (simp[NoAsms, Abbr `actions`, Abbr `ll`, Abbr `i`] >>
      irule le_round_point_available >> simp[] >>
      irule le_reachable_ssa_ordinary_available >> gvs[EL_MEM]) >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >> simp[] >> strip_tac
  >- (gvs[mk_assign_inst_def] >>
      `def_available_at fn bb (SOME i) v` by
        (simp[Abbr `i`] >> irule le_static_singleton_point_available >>
         simp[] >> metis_tac[]) >>
      fs[Abbr `actions`, Abbr `ll`, Abbr `i`] >>
      drule_all le_round_point_available >> simp[]) 
  >- (gvs[mk_assign_inst_def] >>
      `?pa. MEM pa actions /\ pa.pa_phi_out = phi_out /\
        fn_dominates fn pa.pa_join_lbl bb.bb_label` by
        (simp[Abbr `actions`] >> irule le_action_lookup_join_dominates >>
         simp[Abbr `i`] >> metis_tac[]) >>
      `fn_reachable fn pa.pa_join_lbl` by
        metis_tac[fn_dominates_dom_reachable] >>
      `?jb. lookup_block pa.pa_join_lbl fn.fn_blocks = SOME jb` by
        (qpat_x_assum `fn_reachable fn pa.pa_join_lbl` mp_tac >>
         pure_rewrite_tac[fn_reachable_def] >> strip_tac >>
         qpat_x_assum `RTC _ _ pa.pa_join_lbl` mp_tac >>
         once_rewrite_tac[relationTheory.RTC_CASES2] >> strip_tac
         >- (gvs[fn_entry_label_def, entry_block_def] >>
             Cases_on `fn.fn_blocks` >> gvs[] >>
             rename1 `hd :: tl` >> qexists `hd` >>
             irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
         fs[fn_cfg_edge_def, wf_function_def] >>
         `MEM pa.pa_join_lbl (fn_labels fn)` by metis_tac[fn_succs_closed_def] >>
         gvs[fn_labels_def, MEM_MAP] >> metis_tac[MEM_lookup_block]) >>
      `MEM jb fn.fn_blocks /\ jb.bb_label = pa.pa_join_lbl` by
        metis_tac[lookup_block_MEM, lookup_block_label] >>
      `?phi. MEM phi (phis_for_block actions jb.bb_label) /\
        MEM phi_out phi.inst_outputs` by
        (simp[phis_for_block_def, MEM_MAP, MEM_FILTER] >>
         qexists `<|inst_id := pa.pa_phi_id; inst_opcode := PHI;
           inst_operands := pa.pa_phi_ops; inst_outputs := [pa.pa_phi_out]|>` >>
         simp[] >> metis_tac[]) >>
      fs[Abbr `actions`, Abbr `ll`, Abbr `i`] >>
      metis_tac[le_round_generated_output_available]) >>
  gvs[mk_nop_inst_def]
QED

Theorem le_round_preserves_reachable_ssa:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!pa i.
    MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx
      (cfg_analyze fn) (load_analyze ctx fn) fn) /\
    MEM i (fn_insts fn) ==> ~MEM pa.pa_phi_out i.inst_outputs) ==>
  le_reachable_ssa (load_elim_one ctx (cfg_analyze fn) fn)
Proof
  strip_tac >>
  qabbrev_tac `actions = collect_phi_actions (fn_max_inst_id fn) ctx
    (cfg_analyze fn) (load_analyze ctx fn) fn` >>
  qabbrev_tac `tr = analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend actions) (\ll i. [load_elim_inst ctx actions ll i])` >>
  `!b. (tr b).bb_label = b.bb_label` by
    simp[Abbr `tr`, analysis_block_transform_prepend_def] >>
  `(load_elim_one ctx (cfg_analyze fn) fn).fn_blocks = MAP tr fn.fn_blocks` by
    simp[load_elim_one_def, analysis_function_transform_prepend_def,
      function_map_transform_def, Abbr `actions`, Abbr `tr`] >>
  simp[le_reachable_ssa_def] >> conj_tac
  >- (irule le_round_preserves_ssa_form >>
      metis_tac[le_reachable_ssa_unique]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[MEM_MAP] >>
      rename1 `MEM b fn.fn_blocks` >>
      `MEM inst (phis_for_block actions b.bb_label) \/
       ?n. n < LENGTH b.bb_instructions /\
        inst = load_elim_inst ctx actions
          (df_at NONE (load_analyze ctx fn) b.bb_label n)
          (EL n b.bb_instructions)` by
        (irule le_prepend_member_cases >> gvs[Abbr `tr`])
      >- (drule phis_for_block_member >> strip_tac >> gvs[]) >>
      gvs[] >>
      `fn_reachable fn b.bb_label` by metis_tac[le_round_reachable] >>
      ` (EL n b.bb_instructions).inst_opcode <> PHI` by
        metis_tac[le_configured_phi_classification] >>
      simp[Abbr `tr`, Abbr `actions`] >>
      irule le_round_mapped_ordinary_available >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> rename1 `MEM b fn.fn_blocks` >>
  `MEM inst (phis_for_block actions b.bb_label) \/
   ?n. n < LENGTH b.bb_instructions /\
    inst = load_elim_inst ctx actions
      (df_at NONE (load_analyze ctx fn) b.bb_label n)
      (EL n b.bb_instructions)` by
    (irule le_prepend_member_cases >> gvs[Abbr `tr`])
  >- ( `phi_edge_uses_wf (load_elim_one ctx (cfg_analyze fn) fn) (tr b) inst` by
         (irule le_generated_phi_edge_uses_wf >> gvs[Abbr `actions`]) >>
       fs[phi_edge_uses_wf_def] >>
       conj_tac >- metis_tac[] >>
       rpt strip_tac >>
       qpat_x_assum `!pred v. MEM _ _ ==> _` drule >> strip_tac >>
       qexists `pred_bb` >> gvs[MEM_MAP] >> metis_tac[]) >>
  ` (EL n b.bb_instructions).inst_opcode = PHI` by
    metis_tac[le_configured_phi_classification] >>
  `inst = EL n b.bb_instructions` by
    metis_tac[le_configured_phi_unchanged] >> gvs[] >>
  `MEM (EL n b.bb_instructions) b.bb_instructions` by simp[EL_MEM] >>
  conj_tac >- metis_tac[le_reachable_ssa_phi_shape] >>
  conj_tac >- metis_tac[le_reachable_ssa_phi_distinct] >>
  conj_tac >- metis_tac[le_reachable_ssa_phi_edges, le_round_cfg_edge] >>
  rpt strip_tac >>
  drule_all le_round_original_phi_reachable_input_available >> strip_tac >>
  qexists `pb` >> gvs[MEM_MAP] >> metis_tac[]
QED
