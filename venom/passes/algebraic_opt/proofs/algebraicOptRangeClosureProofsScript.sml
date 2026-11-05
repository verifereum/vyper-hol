Theory algebraicOptRangeClosureProofs
Ancestors
  assertElimProofs algebraicOptRangeConditionProofs venomWf venomInst
  rangeAnalysisDefs rangeAnalysisProofs sccpCorrectnessProofs sccpProofsBase
  algebraicOptReachabilityProofs algebraicOptTraceProofs cfgAnalysisProps list

Theorem ao_range_exit_boundary_sound:
  !fn bb s.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    bb.bb_instructions <> [] /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label
                   (LENGTH bb.bb_instructions)) s ==>
    ?rs. df_widen_boundary NONE (range_analyze fn) bb.bb_label = SOME rs /\
         in_range_state rs s.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
  `?exit_rs. df_widen_at NONE (range_analyze fn) bb.bb_label
                (LENGTH bb.bb_instructions) = SOME exit_rs` by
    (irule (SIMP_RULE std_ss [LET_THM] range_widen_at_some) >>
     simp[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_all (cj 2 (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs)) >> simp[] >> strip_tac >>
  Cases_on `df_widen_boundary NONE (range_analyze fn) bb.bb_label`
  >- gvs[range_join_opt_def] >>
  rename1 `df_widen_boundary NONE (range_analyze fn) bb.bb_label = SOME rs` >>
  qexists_tac `rs` >> simp[] >>
  gvs[] >> drule range_join_opt_some_sound_right >>
  disch_then (qspec_then `SOME rs` mp_tac) >>
  gvs[range_sound_def]
QED

Theorem ao_source_prefix_index_bound:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    s0.vs_inst_idx = 0 ==>
    !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ ~phase ==>
         s.vs_inst_idx <= LENGTH bb.bb_instructions
Proof
  ho_match_mp_tac algebraicOptReachabilityProofsTheory.ao_source_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >- simp[]
  >- (rpt strip_tac >>
      drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
      strip_tac >> gvs[] >>
      metis_tac[venomExecProofsTheory.phi_prefix_length_le])
  >- (rpt strip_tac >>
      drule_all venomInstPropsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[] >>
      gvs[get_instruction_def, AllCaseEqs()])
  >> simp[]
QED

Theorem ao_terminator_final_position:
  !fn bb idx inst.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    get_instruction bb idx = SOME inst /\ is_terminator inst.inst_opcode ==>
    SUC idx = LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by metis_tac[bb_well_formed_def] >>
  decide_tac
QED

Theorem ao_source_prefix_dfs:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb ==>
    MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  ho_match_mp_tac ao_source_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- metis_tac[entry_label_in_dfs_pre]
  >- (drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
      strip_tac >> gvs[])
  >- (drule_all venomInstPropsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[])
  >> rename1 `step_inst k ctx inst s = OK t` >>
  `ao_source_step ctx fn (k,F,s) (k,T,t)` by
       (simp[Once ao_source_step_cases] >> metis_tac[]) >>
  drule_all ao_source_step_exit_cfg >> strip_tac >>
  metis_tac[fn_cfg_edge_in_dfs_pre]
QED

Theorem ao_source_prefix_block:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s /\
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >> drule_all ao_source_prefix_dfs >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) s.vs_current_bb` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all cfg_analyze_reachable_in_labels >>
  simp[fn_labels_def, MEM_MAP] >> strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  qexists_tac `bb` >> irule venomExecPropsTheory.MEM_lookup_block >>
  gvs[wf_function_def, fn_labels_def]
QED

Theorem ao_source_prefix_edge_cfg:
  !ctx fn s0 n k s t.
    ao_source_prefix ctx fn s0 n k F s /\
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    ao_source_step ctx fn (k,F,s) (k,T,t) ==>
    MEM t.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    MEM s.vs_current_bb (cfg_preds_of (cfg_analyze fn) t.vs_current_bb) /\
    ?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb
Proof
  rpt gen_tac >> strip_tac >>
  `ao_source_prefix ctx fn s0 n k T t` by
    (drule ao_source_step_prefix >> simp[] >>
     disch_then drule >> simp[]) >>
  conj_tac >- metis_tac[ao_source_prefix_dfs] >>
  conj_tac
  >- (drule_all ao_source_step_exit_cfg >>
      simp[fn_cfg_edge_def] >> strip_tac >>
      simp[GSYM cfg_edge_symmetry_uncond] >>
      gvs[wf_function_def] >> drule_all bb_succs_in_cfg_succs >> simp[]) >>
  metis_tac[ao_source_prefix_block]
QED
