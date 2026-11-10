Theory loadElimDefinitionCuts
Ancestors
  loadElimStaticGeneration loadElimNormalizeAvailability loadElimKeyShapeInvariant
  loadElimTransferProvenance loadElimDefs venomWf venomInst venomExecProofs
  simplifyCfgPhiRepair simplifyCfgStruct simplifyCfgWfssa list rich_list finite_map
  dfAnalyzeDefs cfgDefs simplifyCfgDataflow
  loadElimReachableSSA loadElimReachableNormalize

Theorem le_first_arrival_no_earlier_dominance:
  is_fn_path fn (pre ++ [db.bb_label]) /\
  fn_entry_label fn = SOME (HD (pre ++ [db.bb_label])) /\
  ~MEM db.bb_label pre /\ MEM gb.bb_label pre ==>
  ~fn_dominates fn db.bb_label gb.bb_label
Proof
  strip_tac >> strip_tac >>
  `is_fn_path fn pre` by
    (irule le_path_append_prefix >> qexists `[db.bb_label]` >> simp[]) >>
  drule_all le_path_member_prefix >> strip_tac >>
  `HD (pre' ++ [gb.bb_label]) = HD (pre ++ [db.bb_label])` by
    (gvs[] >> Cases_on `pre'` >> simp[]) >>
  `MEM db.bb_label (pre' ++ [gb.bb_label])` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  gvs[MEM_APPEND]
QED

Theorem le_first_arrival_no_earlier_available:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  is_fn_path fn (pre ++ [db.bb_label]) /\
  fn_entry_label fn = SOME (HD (pre ++ [db.bb_label])) /\
  ~MEM db.bb_label pre /\ MEM gb fn.fn_blocks /\
  MEM gi gb.bb_instructions /\ MEM gb.bb_label pre ==>
  ~def_available_at fn gb (SOME gi) v
Proof
  strip_tac >> strip_tac >> fs[def_available_at_def] >>
  `def_inst = di` by (metis_tac[ssa_form_output_unique]) >>
  `def_bb = db` by metis_tac[wf_function_instruction_block] >> gvs[] >>
  drule_all le_first_arrival_no_earlier_dominance >> simp[]
QED

Theorem le_first_arrival_no_earlier_output:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  is_fn_path fn (pre ++ [db.bb_label]) /\
  fn_entry_label fn = SOME (HD (pre ++ [db.bb_label])) /\
  ~MEM db.bb_label pre /\ MEM gb fn.fn_blocks /\
  MEM gi gb.bb_instructions /\ MEM gb.bb_label pre ==>
  ~MEM v gi.inst_outputs
Proof
  strip_tac >> strip_tac >>
  `gi = di` by (metis_tac[ssa_form_output_unique]) >>
  `gb = db` by metis_tac[wf_function_instruction_block] >> gvs[]
QED

Theorem le_before_definition_no_available:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  d < LENGTH db.bb_instructions /\ MEM v (EL d db.bb_instructions).inst_outputs /\
  MEM gi (TAKE d db.bb_instructions) ==>
  ~def_available_at fn db (SOME gi) v
Proof
  strip_tac >> strip_tac >> fs[def_available_at_def] >>
  `MEM (EL d db.bb_instructions) db.bb_instructions` by simp[EL_MEM] >>
  `def_inst = EL d db.bb_instructions` by
    (metis_tac[ssa_form_output_unique]) >>
  `def_bb = db` by metis_tac[wf_function_instruction_block] >> gvs[] >>
  `i = d` by
    (irule inst_ids_el_eq >> qexistsl [`db`, `fn`] >>
     gvs[wf_function_def] >> metis_tac[]) >> gvs[] >>
  `?k. k < d /\ k < LENGTH db.bb_instructions /\
       EL k db.bb_instructions = EL j db.bb_instructions` by
    (qpat_x_assum `MEM _ (TAKE d _)` mp_tac >>
     simp[MEM_EL] >> strip_tac >> qexists `n` >> gvs[EL_TAKE]) >>
  `j = k` by
    (irule inst_ids_el_eq >> qexistsl [`db`, `fn`] >>
     gvs[wf_function_def] >> metis_tac[]) >> decide_tac
QED

Theorem le_before_definition_no_output:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  d < LENGTH db.bb_instructions /\ MEM v (EL d db.bb_instructions).inst_outputs /\
  MEM gi (TAKE d db.bb_instructions) ==> ~MEM v gi.inst_outputs
Proof
  strip_tac >> strip_tac >>
  `MEM gi db.bb_instructions` by metis_tac[MEM_TAKE] >>
  `MEM (EL d db.bb_instructions) db.bb_instructions` by simp[EL_MEM] >>
  `gi = EL d db.bb_instructions` by
    (metis_tac[ssa_form_output_unique]) >>
  `?k. k < d /\ k < LENGTH db.bb_instructions /\ EL k db.bb_instructions = gi` by
    (qpat_x_assum `MEM gi (TAKE d _)` mp_tac >>
     simp[MEM_EL] >> strip_tac >> qexists `n` >> gvs[EL_TAKE]) >>
  `k = d` by
    (irule inst_ids_el_eq >> qexistsl [`db`, `fn`] >>
     gvs[wf_function_def] >> metis_tac[]) >> decide_tac
QED

Theorem le_first_arrival_no_available:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  d < LENGTH db.bb_instructions /\ MEM v (EL d db.bb_instructions).inst_outputs /\
  is_fn_path fn (pre ++ [db.bb_label]) /\
  fn_entry_label fn = SOME (HD (pre ++ [db.bb_label])) /\
  ~MEM db.bb_label pre /\ MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  (MEM gb.bb_label pre \/ (gb = db /\ MEM gi (TAKE d db.bb_instructions))) ==>
  ~def_available_at fn gb (SOME gi) v
Proof
  strip_tac
  >- (irule le_first_arrival_no_earlier_available >> simp[] >>
      qexistsl [`db`, `EL d db.bb_instructions`, `pre`] >> simp[EL_MEM]) >>
  gvs[] >> irule le_before_definition_no_available >> metis_tac[]
QED

Theorem le_first_arrival_no_output:
  wf_function fn /\ ssa_form fn /\ MEM db fn.fn_blocks /\
  d < LENGTH db.bb_instructions /\ MEM v (EL d db.bb_instructions).inst_outputs /\
  is_fn_path fn (pre ++ [db.bb_label]) /\
  fn_entry_label fn = SOME (HD (pre ++ [db.bb_label])) /\
  ~MEM db.bb_label pre /\ MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  (MEM gb.bb_label pre \/ (gb = db /\ MEM gi (TAKE d db.bb_instructions))) ==>
  ~MEM v gi.inst_outputs
Proof
  strip_tac
  >- (irule le_first_arrival_no_earlier_output >> simp[] >>
      qexistsl [`db`, `EL d db.bb_instructions`, `fn`, `gb`, `pre`] >> simp[EL_MEM]) >>
  gvs[] >> irule le_before_definition_no_output >> metis_tac[]
QED

Theorem le_generator_variable_available:
  le_configured_context ctx /\ le_reachable_ssa fn /\
  MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  fn_reachable fn gb.bb_label /\
  le_transfer_generates ctx gi key (Var v) ==>
  MEM v gi.inst_outputs \/ def_available_at fn gb (SOME gi) v
Proof
  strip_tac >> qpat_x_assum `le_transfer_generates _ _ _ _` mp_tac >>
  simp[le_transfer_generates_def] >> strip_tac >- simp[] >>
  disj2_tac >>
  `gi.inst_opcode <> PHI` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  irule le_reachable_ssa_ordinary_available >> simp[]
QED

Theorem le_generator_key_variable_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  fn_reachable fn gb.bb_label /\
  le_transfer_generates ctx gi (LK_Op (Var v)) op ==>
  def_available_at fn gb (SOME gi) v
Proof
  strip_tac >>
  `gi.inst_opcode <> PHI` by
    (gvs[le_transfer_generates_def, le_configured_context_def,
      memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]) >>
  `?addr. MEM addr gi.inst_operands /\
     normalize_operand (dfg_build_function fn) [] addr = Var v` by
    (qpat_x_assum `le_transfer_generates _ _ _ _` mp_tac >>
     simp[le_transfer_generates_def, load_get_read_key_def, load_get_write_key_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]) >>
  irule le_reachable_normalize_ordinary_use_available >> metis_tac[]
QED

Theorem le_generator_key_variable_available_global:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM gb fn.fn_blocks /\ MEM gi gb.bb_instructions /\
  le_transfer_generates ctx gi (LK_Op (Var v)) op ==>
  def_available_at fn gb (SOME gi) v
Proof
  strip_tac >>
  `gi.inst_opcode <> PHI` by
    (gvs[le_transfer_generates_def, le_configured_context_def,
      memory_config_def, storage_config_def, transient_config_def,
      dload_config_def, calldataload_config_def]) >>
  `?addr. MEM addr gi.inst_operands /\
     normalize_operand (dfg_build_function fn) [] addr = Var v` by
    (qpat_x_assum `le_transfer_generates _ _ _ _` mp_tac >>
     simp[le_transfer_generates_def, load_get_read_key_def, load_get_write_key_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]) >>
  irule le_normalize_ordinary_use_available >> metis_tac[]
QED

Theorem le_ordinary_definition_value_cut:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  n < LENGTH bb.bb_instructions /\
  MEM v (EL n bb.bb_instructions).inst_outputs /\
  (EL n bb.bb_instructions).inst_opcode <> PHI ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key <> SOME [Var v]
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
  qpat_assum `fn_reachable fn bb.bb_label` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_at (Pat `FLOOKUP _ _ = SOME [_]`) le_static_path_singleton_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- ( `MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      `fn_reachable fn gb.bb_label` by
        (irule entry_path_member_reachable >>
         qexistsl [`HD (pre ++ [bb.bb_label])`, `pre ++ [bb.bb_label]`] >>
         simp[]) >>
       drule_all le_generator_variable_available >> strip_tac
       >- (drule_all le_first_arrival_no_earlier_output >> simp[EL_MEM]) >>
       drule_all le_first_arrival_no_earlier_available >> simp[EL_MEM]) >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  drule_all le_generator_variable_available >> strip_tac
  >- (drule_all le_before_definition_no_output >> simp[]) >>
  drule_all le_before_definition_no_available >> simp[]
QED

Theorem le_phi_definition_value_cut:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM di bb.bb_instructions /\ di.inst_opcode = PHI /\ MEM v di.inst_outputs ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) key <> SOME [Var v]
Proof
  strip_tac >> strip_tac >> `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
  qpat_assum `fn_reachable fn bb.bb_label` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  drule_at (Pat `FLOOKUP _ _ = SOME [_]`) le_static_path_singleton_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (`MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      `fn_reachable fn gb.bb_label` by
        (irule entry_path_member_reachable >>
         qexistsl [`HD (pre ++ [bb.bb_label])`, `pre ++ [bb.bb_label]`] >>
         simp[]) >>
      drule_all le_generator_variable_available >> strip_tac
      >- (drule_all le_first_arrival_no_earlier_output >> simp[]) >>
      drule_all le_first_arrival_no_earlier_available >> simp[]) >> gvs[]
QED

Theorem le_ordinary_definition_key_cut:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  n < LENGTH bb.bb_instructions /\
  MEM v (EL n bb.bb_instructions).inst_outputs /\
  (EL n bb.bb_instructions).inst_opcode <> PHI /\
  ctx.lctx_dfg = dfg_build_function fn ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) (LK_Op (Var v)) = NONE
Proof
  strip_tac >>
  Cases_on `FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) (LK_Op (Var v))` >- simp[] >>
  `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
  qpat_assum `fn_reachable fn bb.bb_label` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >> drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) le_static_path_presence_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (`MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      `fn_reachable fn gb.bb_label` by
        (irule entry_path_member_reachable >>
         qexistsl [`HD (pre ++ [bb.bb_label])`, `pre ++ [bb.bb_label]`] >>
         simp[]) >>
      drule_all le_generator_key_variable_available >> strip_tac >>
      drule_all le_first_arrival_no_earlier_available >> simp[]) >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  drule_all le_generator_key_variable_available >> strip_tac >>
  drule_all le_before_definition_no_available >> simp[]
QED

Theorem le_phi_definition_key_cut:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM di bb.bb_instructions /\ di.inst_opcode = PHI /\ MEM v di.inst_outputs /\
  ctx.lctx_dfg = dfg_build_function fn ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) (LK_Op (Var v)) = NONE
Proof
  strip_tac >>
  Cases_on `FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) (LK_Op (Var v))` >- simp[] >>
  `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
  qpat_assum `fn_reachable fn bb.bb_label` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >> drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [bb.bb_label]))` by metis_tac[] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) le_static_path_presence_generation >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (`MEM gb.bb_label pre` by (gvs[EL_APPEND1] >> metis_tac[EL_MEM]) >>
      `fn_reachable fn gb.bb_label` by
        (irule entry_path_member_reachable >>
         qexistsl [`HD (pre ++ [bb.bb_label])`, `pre ++ [bb.bb_label]`] >>
         simp[]) >>
      drule_all le_generator_key_variable_available >> strip_tac >>
      drule_all le_first_arrival_no_earlier_available >> simp[]) >> gvs[]
QED
