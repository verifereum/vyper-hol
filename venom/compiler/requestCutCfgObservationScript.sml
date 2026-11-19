Theory requestCutCfgObservation
Ancestors
  o1ContractCfgNorm
  o1PassLift cfgNormDefs cfgNormSupplyProofs venomFnScheduleRunner venomWf
  venomInst irSupply cfgNormSupplySim contextCodegenRel venomExecSemantics
  venomExecProofs venomStepProps ctxLookupAgreeHelpers o1ContractCfgNormStep
  o1PassContract unitMemInv unitShapeDefs venomRetProps o1ComposeSupport
  venomWfProps staticAbortDefs

Theorem supply_frame_body_projection_rf_observation_under_requests:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_frame_body C fn fn' s pred target split repls s0 inst' v /\
  inst_mem_ranges inst' v <> [] /\ ~in_revert_forward fn' v ==>
  ?inst a. frame_reach C fn s0 inst a /\ ~in_revert_forward fn a /\
    mem_corr inst a inst' v /\
    (in_static_abort_prefix fn a \/ ~P a.vs_requests ==>
      in_static_abort_prefix fn' v \/ ~P v.vs_requests)
Proof
  strip_tac >> drule_all supply_frame_body_witness >> strip_tac >>
  `MEM inst bb.bb_instructions /\ a.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[active_inst_def] >>
     `bb' = bb` by metis_tac[same_label_same_block] >>
     gvs[] >> metis_tac[listTheory.EL_MEM]) >>
  `inst_wf inst /\ label_positions_ok inst /\
   EVERY label_positions_ok bb.bb_instructions` by
    (drule_all EVERY_fn_block >>
     gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward fn a` by
    (strip_tac >> gvs[contextCodegenRelTheory.in_revert_forward_def] >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[] >>
     `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
     `split.bb_label <> bb.bb_label` by
       (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
     `lookup_block bb.bb_label fn'.fn_blocks =
        SOME (supply_block_image pred target split repls bb)` by
       (irule insert_split_supply_image_lookup >> metis_tac[]) >>
     `revert_forward_at (supply_block_image pred target split repls bb) v.vs_inst_idx` by
       (irule supply_block_image_revert_forward_at >> metis_tac[]) >> metis_tac[]) >>
  `in_static_abort_prefix fn a ==> in_static_abort_prefix fn' v` by
    (strip_tac >> gvs[in_static_abort_prefix_def] >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[] >>
     `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
     `split.bb_label <> bb.bb_label` by
       (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
     `lookup_block bb.bb_label fn'.fn_blocks =
        SOME (supply_block_image pred target split repls bb)` by
       (irule insert_split_supply_image_lookup >> metis_tac[]) >>
     simp[] >> conj_tac
     >- gvs[supply_state_agree_def, stateFrameTheory.execution_frame_def] >>
     gvs[static_abort_at_def] >>
     metis_tac[supply_block_image_static_abort_pair]) >>
  `a.vs_requests = v.vs_requests` by
    gvs[supply_state_agree_def, stateFrameTheory.execution_frame_def] >>
  `~MEM inst.inst_opcode [PHI; JMP; JNZ]` by
    (strip_tac >> `inst_mem_ranges inst' v = []` by
       (irule supply_inst_mem_ranges_empty >> gvs[]) >> gvs[]) >>
  `inst' = inst` by
    (gvs[] >> irule supply_block_image_index_unchanged >> simp[]) >>
  `mem_corr inst a inst' v` by
    (gvs[] >> metis_tac[supply_unchanged_inst_projection]) >>
  qexistsl [`inst`, `a`] >> simp[] >> metis_tac[]
QED


Theorem insert_split_supply_frame_sim_rf_observation_under_requests:
  ctx_bisim C C' /\ wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C' fn fn'
Proof
  strip_tac >> simp[frame_sim_rf_observation_def] >> rpt strip_tac >>
  rename1 `frame_reach C' fn' s0 inst' observed` >>
  `frame_reach C fn' s0 inst' observed` by
    (drule supply_frame_reach_ctx_back >> simp[]) >>
  `supply_frame_phase C fn fn' s pred target split repls s0 inst' observed` by
    metis_tac[supply_frame_reach_phase] >>
  gvs[supply_frame_phase_def]
  >- (irule supply_frame_body_projection_rf_observation_under_requests >> metis_tac[]) >>
  drule supply_frame_split_witness >> strip_tac >>
  `MEM inst'.inst_opcode [ASSIGN; JMP]` by
    (drule_all supply_split_index_shape >> gvs[] >> metis_tac[]) >>
  `inst_mem_ranges inst' observed = []` by
    (irule supply_inst_mem_ranges_empty >> gvs[]) >> gvs[]
QED


Theorem supply_frame_sim_rf_observation_refl_under_requests:
  fn_inst_wf fn ==>
  frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C fn fn
Proof
  simp[frame_sim_rf_observation_def] >> rpt strip_tac >>
  rename1 `frame_reach C fn s0 inst' observed` >>
  `active_inst fn inst' observed` by metis_tac[supply_frame_reach_prefix] >>
  `inst_wf inst'` by
    (gvs[active_inst_def, fn_inst_wf_def] >> metis_tac[listTheory.MEM_EL]) >>
  metis_tac[supply_mem_corr_refl]
QED


Theorem supply_round_frame_sim_rf_observation_under_requests:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C fn fn'
Proof
  strip_tac >>
  `wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[supply_frame_sim_rf_observation_refl_under_requests] >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
  `rest = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `ctx_bisim C C` by
    (simp[ctx_bisim_def] >> metis_tac[supply_run_blocks_frame_refl]) >>
  irule insert_split_supply_frame_sim_rf_observation_under_requests >> metis_tac[]
QED


Theorem supply_iter_frame_sim_rf_observation_under_requests:
  !n s fn fn' s'.
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C fn fn'
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def] >>
      metis_tac[supply_frame_sim_rf_observation_refl_under_requests, supply_norm_inv_projections]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (mid,changed,s1)` >>
  `supply_norm_inv s1 mid /\ EVERY label_positions_ok (fn_insts mid) /\
   fn_entry_label mid = fn_entry_label fn` by metis_tac[supply_round_semantics] >>
  `frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C fn mid` by
    metis_tac[supply_round_frame_sim_rf_observation_under_requests] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- metis_tac[frame_sim_rf_observation_trans] >> metis_tac[]
QED


Theorem cfg_norm_function_supply_frame_sim_rf_observation_under_requests:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C' fn fn'
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  `supply_norm_inv s fn` by simp[supply_norm_inv_def] >>
  `frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) L C C fn fn'` by
    metis_tac[supply_iter_frame_sim_rf_observation_under_requests] >>
  simp[frame_sim_rf_observation_def] >> rpt strip_tac >>
  rename1 `frame_reach C' fn' s0 inst' observed` >>
  `frame_reach C fn' s0 inst' observed` by
    (drule supply_frame_reach_ctx_back >> simp[]) >>
  gvs[frame_sim_rf_observation_def] >> metis_tac[]
QED


Theorem frame_sim_rf_observation_mem_inv_lowered_abort_under_requests:
  ctx_bisim C C' /\
  LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
    fn_entry_label fn' = fn_entry_label fn /\
    frame_sim vs.vs_labels C C' fn fn' /\
    frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) vs.vs_labels C C' fn fn')
    C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s.
    (in_static_abort_prefix fn s \/ ~P s.vs_requests) \/ lowered_mem_fact eom ctx fn inst s) C vs ==>
  mem_inv (\ctx fn inst s.
    (in_static_abort_prefix fn s \/ ~P s.vs_requests) \/ lowered_mem_fact eom ctx fn inst s) C' vs
Proof
  strip_tac >>
  `!nm fn fn'. lookup_function nm C.ctx_functions = SOME fn /\
               lookup_function nm C'.ctx_functions = SOME fn' ==>
     frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) vs.vs_labels C C' fn fn'` by
    (rpt strip_tac >> drule list_rel_lookup_function >> simp[] >>
     disch_then (qspec_then `nm` mp_tac) >> simp[]) >>
  `LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
     fn_entry_label fn' = fn_entry_label fn /\
     frame_sim vs.vs_labels C C' fn fn') C.ctx_functions C'.ctx_functions` by
    (irule listTheory.LIST_REL_mono >>
     goal_assum (first_assum o mp_then Any mp_tac) >> simp[]) >>
  fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule list_rel_lookup_function >> simp[] >>
      disch_then (qspec_then `name` mp_tac) >>
      Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
      strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `inst_mem_ranges inst s = [] \/ in_revert_forward fn' s`
  >- gvs[lowered_mem_fact_def, lowered_mem_ok_def] >>
  drule_all frame_sim_raw_origins >> strip_tac >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  rw[frame_origin_def] >> rename1 `fn_entry_state src s0` >>
  `frame_sim_rf_observation (\f st. in_static_abort_prefix f st \/ ~P st.vs_requests) vs.vs_labels C C' src fn'`
    by metis_tac[] >>
  fs[frame_sim_rf_observation_def] >>
  first_x_assum (qspecl_then [`s0`, `inst`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `frame_reach C src s0 src_inst src_state` >>
  `raw_reachable vs C src src_inst src_state` by
    metis_tac[frame_reach_raw_reachable] >>
  `(in_static_abort_prefix src src_state \/ ~P src_state.vs_requests) \/
   lowered_mem_fact eom C src src_inst src_state` by metis_tac[] >>
  metis_tac[mem_corr_closed_rf_lowered_mem_fact, mem_corr_closed_rf_transfer]
QED


Theorem cfg_norm_stage_mem_inv_lowered_abort_under_requests:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s.
    (in_static_abort_prefix fn s \/ ~P s.vs_requests) \/ lowered_mem_fact eom ctx fn inst s) C vs ==>
  mem_inv (\ctx fn inst s.
    (in_static_abort_prefix fn s \/ ~P s.vs_requests) \/ lowered_mem_fact eom ctx fn inst s) C' vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by (irule cfg_norm_stage_bisim >> metis_tac[]) >>
  drule cfg_norm_stage_functions >> strip_tac >>
  irule frame_sim_rf_observation_mem_inv_lowered_abort_under_requests >> simp[] >>
  qexists_tac `C` >> simp[] >>
  gvs[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule cfg_norm_function_supply_identity >> strip_tac >> simp[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by simp[listTheory.EL_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >>
  metis_tac[cfg_norm_function_supply_frame_sim,
            cfg_norm_function_supply_frame_sim_rf_observation_under_requests]
QED
