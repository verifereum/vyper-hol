Theory loadElimNormalizedCuts
Ancestors
  loadElimSelectedGeneration loadElimDefinitionCuts loadElimNormalizeAvailability
  loadElimNormalizeHelpers loadElimTransferProvenance loadElimDefs loadElimConfiguredGeneration loadElimKeyShapeInvariant
  dfgDefs dfgAnalysisProps venomWf venomInst venomExecProofs
  simplifyCfgLabelProps simplifyCfgPhiRepair simplifyCfgWfssa simplifyCfgStruct simplifyCfgPhiSemantics
  finite_map list rich_list dfAnalyzeDefs cfgDefs

Theorem le_ssa_output_def:
  wf_ssa fn /\ MEM gi (fn_insts fn) /\ MEM out gi.inst_outputs ==>
  dfg_get_def (dfg_build_function fn) out = SOME gi
Proof
  strip_tac >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst' = gi` by
    (gvs[fn_insts_def, fn_insts_blocks_mem, wf_ssa_def] >>
     metis_tac[ssa_form_output_unique]) >>
  gvs[]
QED

Theorem le_nonassign_output_normalize:
  wf_ssa fn /\ MEM gi (fn_insts fn) /\ MEM out gi.inst_outputs /\
  gi.inst_opcode <> ASSIGN ==>
  normalize_operand (dfg_build_function fn) [] (Var out) = Var out
Proof
  strip_tac >> drule_all le_ssa_output_def >>
  simp[dfg_get_def_def] >> strip_tac >>
  simp[Once normalize_operand_def]
QED

Theorem le_nonassign_output_chain_valid:
  wf_ssa fn /\ MEM gi (fn_insts fn) /\ MEM out gi.inst_outputs /\
  gi.inst_opcode <> ASSIGN ==>
  le_chain_valid (dfg_build_function fn) visited (Var out) s
Proof
  strip_tac >> drule_all le_ssa_output_def >>
  simp[dfg_get_def_def] >> strip_tac >>
  simp[Once le_chain_valid_def]
QED

Theorem le_normalized_generator_available:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  le_transfer_generates ctx gi key op /\
  normalize_operand ctx.lctx_dfg [] op = Var v ==>
  MEM v gi.inst_outputs \/ def_available_at fn gb (SOME gi) v
Proof
  strip_tac >>
  qpat_x_assum `le_transfer_generates _ _ _ _` mp_tac >>
  simp[le_transfer_generates_def] >> strip_tac
  >- (gvs[] >>
      `gi.inst_opcode <> ASSIGN` by
        (drule_all le_configured_load_opcode >> simp[] >> strip_tac >> gvs[]) >>
      `MEM gi (fn_insts fn)` by
        (simp[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
      `MEM out gi.inst_outputs` by simp[] >>
      drule_all le_nonassign_output_normalize >> strip_tac >> gvs[]) >>
  disj2_tac >>
  `gi.inst_opcode <> PHI` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  irule le_normalize_ordinary_use_available >> metis_tac[MEM]
QED

Theorem le_ordinary_definition_normalized_cut:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  n < LENGTH bb.bb_instructions /\ MEM v (EL n bb.bb_instructions).inst_outputs /\
  (EL n bb.bb_instructions).inst_opcode <> PHI /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME vs ==>
  ~EVERY (\op. normalize_operand ctx.lctx_dfg [] op = Var v) vs
Proof
  strip_tac >> strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) le_static_path_member_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `op` assume_tac) >>
  `normalize_operand ctx.lctx_dfg [] op = Var v` by fs[EVERY_MEM] >>
  qpat_x_assum `MEM op vs /\ _` strip_assume_tac
  >- (`MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      drule_all le_normalized_generator_available >> strip_tac
      >- (drule_all le_first_arrival_no_earlier_output >> simp[EL_MEM]) >>
      drule_all le_first_arrival_no_earlier_available >> simp[EL_MEM]) >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  drule_all le_normalized_generator_available >> strip_tac
  >- (drule_all le_before_definition_no_output >> simp[]) >>
  drule_all le_before_definition_no_available >> simp[]
QED

Theorem le_phi_definition_normalized_cut:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM di bb.bb_instructions /\ di.inst_opcode = PHI /\ MEM v di.inst_outputs /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) key = SOME vs ==>
  ~EVERY (\op. normalize_operand ctx.lctx_dfg [] op = Var v) vs
Proof
  strip_tac >> strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) le_static_path_member_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `op` assume_tac) >>
  `normalize_operand ctx.lctx_dfg [] op = Var v` by fs[EVERY_MEM] >>
  qpat_x_assum `MEM op vs /\ _` strip_assume_tac
  >- (`MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      drule_all le_normalized_generator_available >> strip_tac
      >- (drule_all le_first_arrival_no_earlier_output >> simp[]) >>
      drule_all le_first_arrival_no_earlier_available >> simp[]) >>
  gvs[]
QED
