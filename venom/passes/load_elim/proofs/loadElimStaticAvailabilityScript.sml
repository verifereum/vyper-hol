Theory loadElimStaticAvailability
Ancestors
  loadElimStaticGeneration loadElimDefinitionCuts loadElimConvergence
  loadElimNormalizeAvailability loadElimDefs loadElimSolverHelpers
  simplifyCfgWfssa simplifyCfgPhiRepair simplifyCfgStruct simplifyCfgDataflow
  loadElimReachableSSA
  venomWf venomInst venomExecProofs dfAnalyzeDefs cfgDefs list rich_list finite_map

Theorem le_path_dominating_prefix[local]:
  is_fn_path fn path /\ fn_entry_label fn = SOME (HD path) /\
  j < LENGTH path /\ fn_dominates fn d (EL j path) ==>
  ?k. k <= j /\ EL k path = d
Proof
  strip_tac >>
  `path = TAKE (SUC j) path ++ DROP (SUC j) path` by simp[] >>
  `is_fn_path fn (TAKE (SUC j) path)` by
    (irule le_path_append_prefix >> metis_tac[]) >>
  `TAKE (SUC j) path <> []` by
    (Cases_on `path` >> gvs[]) >>
  `HD (TAKE (SUC j) path) = HD path` by
    (Cases_on `path` >> gvs[]) >>
  `LAST (TAKE (SUC j) path) = EL j path` by
    (simp[TAKE_SUC, LAST_APPEND]) >>
  `MEM d (TAKE (SUC j) path)` by metis_tac[fn_dominates_def] >>
  fs[MEM_EL] >> qexists `n` >> gvs[EL_TAKE]
QED

Theorem le_path_available_earlier[local]:
  is_fn_path fn path /\ fn_entry_label fn = SOME (HD path) /\
  j < LENGTH path - 1 /\ gb.bb_label = EL j path /\
  def_available_at fn gb (SOME gi) v ==>
  ?k db di. k < LENGTH path - 1 /\ MEM db fn.fn_blocks /\
    db.bb_label = EL k path /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs
Proof
  strip_tac >> fs[def_available_at_def] >>
  `j < LENGTH path` by decide_tac >>
  `fn_dominates fn def_bb.bb_label (EL j path)` by metis_tac[] >>
  drule_all le_path_dominating_prefix >> strip_tac >>
  qexistsl [`k`, `def_bb`, `def_inst`] >> simp[]
QED

Theorem le_path_available_current[local]:
  wf_function fn /\ is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label /\
  MEM bb fn.fn_blocks /\ n <= LENGTH bb.bb_instructions /\
  MEM gi (TAKE n bb.bb_instructions) /\ def_available_at fn bb (SOME gi) v ==>
  (?k db di. k < LENGTH path - 1 /\ MEM db fn.fn_blocks /\
    db.bb_label = EL k path /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs) \/
  (?i. i < n /\ MEM v (EL i bb.bb_instructions).inst_outputs)
Proof
  strip_tac >> fs[def_available_at_def] >>
  `MEM def_bb.bb_label path` by metis_tac[fn_dominates_def] >>
  qpat_x_assum `MEM def_bb.bb_label path`
    (qx_choose_then `p` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  Cases_on `p < LENGTH path - 1`
  >- (disj1_tac >> qexistsl [`p`, `def_bb`, `def_inst`] >> simp[]) >>
  `p = LENGTH path - 1` by decide_tac >>
  `PRE (LENGTH path) = LENGTH path - 1` by decide_tac >>
  `def_bb.bb_label = bb.bb_label` by metis_tac[LAST_EL] >>
  `def_bb = bb` by metis_tac[same_label_same_block] >> gvs[] >>
  `?k. k < n /\ EL k bb.bb_instructions = EL j bb.bb_instructions` by
    (qpat_x_assum `MEM _ (TAKE n _)` mp_tac >>
     simp[MEM_EL] >> strip_tac >> qexists `n'` >> gvs[EL_TAKE]) >>
  `k = j` by
    (irule inst_ids_el_eq >> qexistsl [`bb`, `fn`] >>
     gvs[wf_function_def] >> metis_tac[]) >>
  disj2_tac >> qexists `i` >> simp[]
QED

Theorem le_static_singleton_path_definition[local]:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ is_fn_path fn path /\ path <> [] /\
  fn_entry_label fn = SOME (HD path) /\ LAST path = bb.bb_label /\
  MEM bb fn.fn_blocks /\ n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME [Var v] ==>
  (?k db di. k < LENGTH path - 1 /\ MEM db fn.fn_blocks /\
    db.bb_label = EL k path /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs) \/
  (?i. i < n /\ MEM v (EL i bb.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn)` by
    metis_tac[le_load_analyze_fixpoint, le_solver_process_def] >>
  drule_at (Pat `FLOOKUP _ _ = SOME [_]`) le_static_path_singleton_generation >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (`fn_reachable fn gb.bb_label` by
        (irule entry_path_member_reachable >>
         qexistsl [`HD path`, `path`] >> simp[] >>
         simp[EL_MEM]) >>
      drule_all le_generator_variable_available >> strip_tac
      >- (disj1_tac >> qexistsl [`j`, `gb`, `inst`] >> simp[]) >>
      disj1_tac >> irule le_path_available_earlier >> metis_tac[]) >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_TAKE] >>
  `fn_reachable fn bb.bb_label` by
    (irule entry_path_member_reachable >>
     qexistsl [`HD path`, `path`] >> simp[] >> metis_tac[LAST_MEM]) >>
  drule_all le_generator_variable_available >> strip_tac
  >- (disj2_tac >>
      qpat_x_assum `MEM inst (TAKE n _)`
        (qx_choose_then `k` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
      qexists `k` >> gvs[EL_TAKE]) >>
  irule le_path_available_current >> metis_tac[]
QED

Theorem le_static_singleton_point_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ n < LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME [Var v]
  ==> def_available_at fn bb (SOME (EL n bb.bb_instructions)) v
Proof
  strip_tac >> irule def_on_all_paths_available >>
  simp[] >> conj_tac >- metis_tac[le_reachable_ssa_unique] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  `fn_entry_label fn = SOME (HD path)` by metis_tac[] >>
  `n <= LENGTH bb.bb_instructions` by simp[] >>
  drule_all le_static_singleton_path_definition >> strip_tac
  >- metis_tac[] >>
  disj2_tac >> qexists `i` >> simp[] >> qexists `n` >> simp[]
QED

Theorem le_static_singleton_endpoint_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label (LENGTH bb.bb_instructions))) key = SOME [Var v]
  ==> def_available_at fn bb NONE v
Proof
  strip_tac >> irule def_on_all_paths_available >>
  simp[] >> conj_tac >- metis_tac[le_reachable_ssa_unique] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  `fn_entry_label fn = SOME (HD path)` by metis_tac[] >>
  irule le_static_singleton_path_definition >> simp[] >> metis_tac[]
QED
