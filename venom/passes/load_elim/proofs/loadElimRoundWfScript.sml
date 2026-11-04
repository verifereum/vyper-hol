Theory loadElimRoundWf
Ancestors
  loadElimInstWf loadElimActions loadElimStructure loadElimDefs
  analysisSimDefs passSimulationDefs passSimulationProps venomWf venomInst list indexedLists combin removeUnusedSsaProofs

Theorem le_old_transform_wf:
  !ctx actions result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn ==>
    wf_function (analysis_function_transform NONE result
      (\ll inst. [load_elim_inst ctx actions ll inst]) fn)
Proof
  rpt strip_tac >> irule aft_singleton_preserves_wf >>
  simp[le_load_elim_inst_id, le_load_elim_inst_terminator,
       le_load_elim_inst_phi, le_load_elim_inst_terminator_unchanged]
QED

Theorem le_prepend_ids_distinct:
  !ctx cfg result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn ==>
    fn_inst_ids_distinct
      (analysis_function_transform_prepend NONE result
        (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]) fn)
Proof
  rpt strip_tac >>
  drule_all le_old_transform_wf >>
  disch_then (qspecl_then
    [`collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn`, `result`]
    assume_tac) >>
  fs[fn_inst_ids_distinct_def, analysis_function_transform_prepend_def,
     function_map_transform_def, MAP_MAP_o, o_DEF] >>
  `!xs:instruction list. FLAT (MAP (\i. [i.inst_id]) xs) =
      MAP (\i. i.inst_id) xs` by (Induct >> simp[]) >>
  qspecl_then [`fn.fn_blocks`, `NONE`, `result`,
    `phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn)`,
    `\ll inst. [load_elim_inst ctx
      (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]`,
    `\i:instruction. [i.inst_id]`] mp_tac le_abtp_global_distinct >>
  simp[] >> disch_then (fn th => rewrite_tac[th]) >>
  simp[ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (qpat_x_assum `wf_function (analysis_function_transform _ _ _ _)` mp_tac >>
      simp[wf_function_def, fn_inst_ids_distinct_def,
        analysis_function_transform_def, function_map_transform_def,
        MAP_MAP_o, o_DEF]) >>
  conj_tac
  >- (irule le_phis_for_blocks_ids_distinct >>
      fs[wf_function_def, fn_labels_def] >>
      irule le_collect_phi_ids_distinct >> fs[wf_function_def]) >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  drule le_inserted_phi_fresh_id >> strip_tac >>
  qpat_x_assum `MEM i (analysis_block_transform _ _ _ _).bb_instructions` mp_tac >>
  simp[abt_singleton_eq_mapi, MEM_MAPi] >> rpt strip_tac >>
  gvs[le_load_elim_inst_id] >>
  `MEM (EL idx x.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     qexists `x.bb_instructions` >> conj_tac
     >- (qexists `x` >> simp[]) >>
     simp[MEM_EL] >> metis_tac[]) >>
  drule le_fn_max_inst_id_bound >> simp[]
QED

Theorem le_prepend_transform_wf:
  !ctx cfg result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn ==>
    wf_function
      (analysis_function_transform_prepend NONE result
        (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]) fn)
Proof
  rpt strip_tac >>
  `!bb. EVERY (\i. i.inst_opcode = PHI)
      (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn)
        bb.bb_label)` by
    simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
  `!bb. bb_well_formed bb ==>
    bb_well_formed (analysis_block_transform NONE result
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]) bb)` by
    (rpt strip_tac >> rewrite_tac[abt_singleton_eq_mapi] >>
     irule mapi_transform_bb_well_formed >>
     simp[le_load_elim_inst_terminator, le_load_elim_inst_phi]) >>
  rewrite_tac[analysis_function_transform_prepend_def] >>
  irule fmt_preserves_wf_function >> simp[] >> rpt conj_tac
  >- simp[le_abtp_eq, analysis_block_transform_def]
  >- (rpt strip_tac >> irule le_abtp_wf >> simp[])
  >- (rpt strip_tac >> simp[le_abtp_succs] >>
      rewrite_tac[abt_singleton_eq_mapi] >>
      irule mapi_transform_bb_succs >>
      simp[le_load_elim_inst_terminator_unchanged, le_load_elim_inst_terminator]) >>
  metis_tac[le_prepend_ids_distinct, analysis_function_transform_prepend_def]
QED

Theorem le_load_elim_one_wf:
  !ctx cfg fn. le_supported_config ctx.lctx_config /\ wf_function fn ==>
    wf_function (load_elim_one ctx cfg fn)
Proof
  `!actions. load_phi_prepend actions = phis_for_block actions` by
    simp[FUN_EQ_THM, load_phi_prepend_def] >>
  simp[load_elim_one_def, le_prepend_transform_wf]
QED

Theorem le_old_transform_ssa:
  !ctx actions result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn /\ ssa_form fn ==>
    ssa_form (analysis_function_transform NONE result
      (\ll inst. [load_elim_inst ctx actions ll inst]) fn)
Proof
  rpt strip_tac >>
  `wf_function (analysis_function_transform NONE result
      (\ll inst. [load_elim_inst ctx actions ll inst]) fn)` by
    metis_tac[le_old_transform_wf] >>
  rewrite_tac[analysis_function_transform_def] >>
  irule fmt_preserves_ssa_form_general >>
  fs[wf_function_def, analysis_function_transform_def] >>
  rpt strip_tac >>
  gvs[abt_singleton_eq_mapi, MEM_MAPi] >>
  qexists `EL idx bb.bb_instructions` >>
  simp[le_load_elim_inst_id, le_load_elim_inst_outputs, MEM_EL] >>
  metis_tac[]
QED

Theorem le_prepend_transform_ssa:
  !ctx cfg result fn.
    le_supported_config ctx.lctx_config /\ wf_function fn /\ ssa_form fn /\
    le_reserved_names [ctx.lctx_config.lc_load] fn ==>
    ssa_form
      (analysis_function_transform_prepend NONE result
        (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]) fn)
Proof
  rpt strip_tac >>
  drule_all le_old_transform_ssa >>
  disch_then (qspecl_then
    [`collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn`, `result`]
    assume_tac) >>
  pure_rewrite_tac[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
    analysis_function_transform_prepend_def, function_map_transform_def] >>
  pure_rewrite_tac[ir_function_accfupds, combinTheory.K_THM,
    MAP_FLAT, MAP_MAP_o, o_DEF, rich_listTheory.FLAT_FLAT] >>
  BETA_TAC >>
  rewrite_tac[le_abtp_global_distinct, ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (qpat_x_assum `ssa_form (analysis_function_transform _ _ _ _)` mp_tac >>
      simp[ssa_form_def, fn_insts_def, fn_insts_blocks_flat,
        analysis_function_transform_def, function_map_transform_def,
        MAP_FLAT, MAP_MAP_o, o_DEF, rich_listTheory.FLAT_FLAT]) >>
  conj_tac
  >- (irule le_phis_for_blocks_outputs_distinct >>
      fs[wf_function_def, fn_labels_def] >>
      irule le_collect_phi_outputs_distinct >> fs[wf_function_def]) >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  drule le_phis_for_block_source >> strip_tac >>
  drule le_collect_phi_action_inst >> strip_tac >>
  qpat_x_assum `MEM i (analysis_block_transform _ _ _ _).bb_instructions` mp_tac >>
  simp[abt_singleton_eq_mapi, MEM_MAPi] >> rpt strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`ctx`,
    `collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn`,
    `df_at NONE result bb.bb_label idx`, `EL idx bb.bb_instructions`]
    le_load_elim_inst_outputs) >> strip_tac >> gvs[] >>
  qpat_x_assum `le_reserved_names _ _` mp_tac >>
  simp[le_reserved_names_def] >>
  qexists `inst` >> simp[] >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists `EL idx bb.bb_instructions` >> simp[] >>
  qexists `bb` >> simp[MEM_EL] >> metis_tac[]
QED

Theorem le_load_elim_one_ssa:
  !ctx cfg fn.
    le_supported_config ctx.lctx_config /\ wf_function fn /\ ssa_form fn /\
    le_reserved_names [ctx.lctx_config.lc_load] fn ==>
    ssa_form (load_elim_one ctx cfg fn)
Proof
  `!actions. load_phi_prepend actions = phis_for_block actions` by
    simp[FUN_EQ_THM, load_phi_prepend_def] >>
  simp[load_elim_one_def, le_prepend_transform_ssa]
QED

Theorem le_prepend_transform_reserved:
  !ctx cfg result fn ops.
    le_supported_config ctx.lctx_config /\ wf_function fn /\
    EVERY (\op. MEM op le_load_opcodes) ops /\
    ~MEM ctx.lctx_config.lc_load ops /\ le_reserved_names ops fn ==>
    le_reserved_names ops
      (analysis_function_transform_prepend NONE result
        (phis_for_block (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn))
        (\ll inst. [load_elim_inst ctx
          (collect_phi_actions (fn_max_inst_id fn) ctx cfg result fn) ll inst]) fn)
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `phis_for_block actions` >>
  pure_rewrite_tac[le_reserved_names_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM inst (fn_insts _)` mp_tac >>
  simp[fn_insts_def, fn_insts_blocks_flat, analysis_function_transform_prepend_def,
    function_map_transform_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  reverse (gvs[le_abtp_mem])
  >- (drule le_phis_for_block_source >> strip_tac >>
      gvs[EVERY_MEM] >>
      `MEM PHI le_load_opcodes` by metis_tac[] >>
      gvs[le_load_opcodes_def]) >>
  `MEM inst.inst_opcode le_load_opcodes` by fs[EVERY_MEM] >>
  qpat_x_assum `MEM inst (analysis_block_transform _ _ _ _).bb_instructions` mp_tac >>
  simp[abt_singleton_eq_mapi, MEM_MAPi] >> rpt strip_tac >> gvs[] >>
  drule le_load_elim_inst_future_load >> strip_tac >>
  gvs[le_load_elim_inst_id] >>
  `MEM (EL idx y.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     qexists `y.bb_instructions` >> conj_tac
     >- (qexists `y` >> simp[]) >>
     simp[MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `MEM _ (FLAT _)` mp_tac >>
  simp[fn_insts_def, fn_insts_blocks_flat, analysis_function_transform_prepend_def,
    function_map_transform_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  reverse (gvs[le_abtp_mem])
  >- (drule le_phis_for_block_source >> strip_tac >>
      gvs[Abbr `actions`] >>
      `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
      `(EL idx y.bb_instructions).inst_opcode <> ctx.lctx_config.lc_load`
        by metis_tac[] >>
      drule_all le_future_load_action_name_apart >> simp[]) >>
  qpat_x_assum `MEM i (analysis_block_transform _ _ _ _).bb_instructions` mp_tac >>
  simp[abt_singleton_eq_mapi, MEM_MAPi] >> rpt strip_tac >> gvs[] >>
  rename1 `MEM (fresh_phi_var _) (load_elim_inst _ _ _ (EL n y'.bb_instructions)).inst_outputs` >>
  mp_tac (Q.SPECL [`ctx`, `actions`, `df_at NONE result y'.bb_label n`,
    `EL n y'.bb_instructions`] le_load_elim_inst_outputs) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `le_reserved_names _ _` mp_tac >>
  simp[le_reserved_names_def] >>
  qexists `EL idx y.bb_instructions` >> simp[] >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexists `EL n y'.bb_instructions` >> simp[] >>
  qexists `y'` >> simp[MEM_EL] >> metis_tac[]
QED

Theorem le_load_elim_one_reserved:
  !ctx cfg fn ops.
    le_supported_config ctx.lctx_config /\ wf_function fn /\
    EVERY (\op. MEM op le_load_opcodes) ops /\
    ~MEM ctx.lctx_config.lc_load ops /\ le_reserved_names ops fn ==>
    le_reserved_names ops (load_elim_one ctx cfg fn)
Proof
  `!actions. load_phi_prepend actions = phis_for_block actions` by
    simp[FUN_EQ_THM, load_phi_prepend_def] >>
  simp[load_elim_one_def, le_prepend_transform_reserved]
QED

Theorem le_reserved_names_subset:
  !ops other fn.
    le_reserved_names ops fn /\ (!op. MEM op other ==> MEM op ops) ==>
    le_reserved_names other fn
Proof
  simp[le_reserved_names_def] >> metis_tac[]
QED
