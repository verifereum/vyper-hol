Theory loadElimLatestRetention
Ancestors
  loadElimOccurrenceRetention loadElimOccurrencePositions loadElimActionPlacement
  loadElimOccurrence
  loadElimSingletonSuffix loadElimSolverProvenance loadElimGeneratedSupport
  loadElimPhiCapture loadElimActualGeneration loadElimSupportHelpers
  loadElimDefs venomExecProps venomWf list rich_list finite_map pred_set

Theorem le_occ_latest_join_multivalue_retention:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key
    s.vs_current_bb i = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  i.inst_opcode = ctx.lctx_config.lc_load /\ i.inst_operands = [addr] /\
  key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
    (normalize_operand ctx.lctx_dfg []) i /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb s.vs_inst_idx)) key = SOME ops /\ 1 < LENGTH ops /\
  (!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl) ==>
  (!b n fuel x y. MEM (StepOcc b n fuel x y) (PhiOcc bb u p :: suffix) ==>
    ?vs. 1 < LENGTH vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label n)) key = SOME vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label (SUC n))) key = SOME vs) /\
  (!b x y. MEM (PhiOcc b x y) (PhiOcc bb u p :: suffix) ==>
    ?vs. 1 < LENGTH vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label 0)) key = SOME vs)
Proof
  strip_tac >>
  `?lastbb. lookup_block s.vs_current_bb fn.fn_blocks = SOME lastbb /\
    s.vs_inst_idx < LENGTH lastbb.bb_instructions /\
    EL s.vs_inst_idx lastbb.bb_instructions = i` by
    metis_tac[le_occ_prefix_active, le_active_inst_lookup] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb 0)) key = SOME ops` by
    (irule le_analyze_multivalue_origin >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  drule le_occ_suffix_positions >>
  disch_then (qspecl_then [`pre`, `bb`, `u`, `p`, `suffix`] mp_tac) >>
  pure_rewrite_tac [boolTheory.REFL_CLAUSE, boolTheory.IMP_CLAUSES] >> strip_tac >>
  `le_pred_path (cfg_analyze fn) (bb.bb_label :: le_occ_route suffix)` by
    (drule_all loadElimJoinPlacementTheory.le_occ_prefix_pred_route >>
     simp[loadElimOccurrenceCoverageTheory.le_occ_route_append,
       loadElimOccurrenceCoverageTheory.le_occ_route_def] >>
     metis_tac[le_pred_path_suffix]) >>
  `EVERY (\l. ?b. MEM b fn.fn_blocks /\ b.bb_label = l)
    (bb.bb_label :: le_occ_route suffix)` by
    (drule le_occ_prefix_route_blocks >>
     simp[loadElimOccurrenceCoverageTheory.le_occ_route_append,
       loadElimOccurrenceCoverageTheory.le_occ_route_def]) >>
  `~MEM bb.bb_label (le_occ_route suffix)` by
    (strip_tac >> drule le_route_phi_split >> strip_tac >>
     qpat_x_assum `!b x y. MEM (PhiOcc b x y) suffix ==> _`
       (qspecl_then [`bb'`, `u'`, `v`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT ops` by
    (`le_lattice_supported (le_generated_keys ctx (fn_insts fn))
       (le_generated_operands (fn_insts fn))
       (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)` by
       (irule le_analyze_point_supported >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
     fs[le_lattice_supported_def] >> metis_tac[]) >>
  `?a b. MEM a ops /\ MEM b ops /\ a <> b` by
    (Cases_on `ops` >> gvs[] >> Cases_on `t` >> gvs[] >> metis_tac[]) >>
  `find_join_block (cfg_analyze fn) {} s.vs_current_bb = bb.bb_label` by
    metis_tac[le_compute_phi_action_certificate] >>
  `!b. MEM b fn.fn_blocks /\
     MEM b.bb_label (FRONT (bb.bb_label :: le_occ_route suffix)) ==>
     ?ys. 1 < LENGTH ys /\ !n. n <= LENGTH b.bb_instructions ==>
       FLOOKUP (unwrap_load_lattice
         (df_at NONE (load_analyze ctx fn) b.bb_label n)) key = SOME ys` by
    (rpt strip_tac >> irule le_action_partial_suffix_retention >>
     metis_tac[]) >>
  conj_tac
  >- (map_every qx_gen_tac [`blk`, `n`, `fuel`, `x`, `y`] >> strip_tac >>
      `MEM blk fn.fn_blocks /\ n < LENGTH blk.bb_instructions` by
        metis_tac[le_occ_step_static, MEM_APPEND] >>
      qpat_x_assum `!b n fuel x y. MEM (StepOcc b n fuel x y) (PhiOcc bb u p :: suffix) ==> _`
        (qspecl_then [`blk`, `n`, `fuel`, `x`, `y`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac
      >- (qpat_x_assum `!b. MEM b fn.fn_blocks /\ _ ==> _`
            (qspec_then `blk` mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          qexists_tac `ys` >> simp[]) >>
      `n <= s.vs_inst_idx /\ s.vs_inst_idx <= LENGTH lastbb.bb_instructions` by decide_tac >>
      qexists_tac `ops` >> conj_tac >- simp[] >> conj_tac >>
      irule le_analyze_multivalue_prefix >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  map_every qx_gen_tac [`blk`, `x`, `y`] >> strip_tac >>
  `MEM blk fn.fn_blocks` by metis_tac[le_occ_phi_static, MEM_APPEND] >>
  qpat_x_assum `!b x y. MEM (PhiOcc b x y) (PhiOcc bb u p :: suffix) ==> _`
    (qspecl_then [`blk`, `x`, `y`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (qpat_x_assum `!b. MEM b fn.fn_blocks /\ _ ==> _`
        (qspec_then `blk` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qexists_tac `ys` >> simp[]) >>
  qexists_tac `ops` >> metis_tac[]
QED
