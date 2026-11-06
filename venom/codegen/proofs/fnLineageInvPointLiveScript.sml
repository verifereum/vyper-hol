Theory fnLineageInvPointLive
Ancestors fnPlanLineagePath fnPlanLineagePhiActivation fnPlanLineageLiveness livenessAnalysisProps
  venomWf venomInst venomExecProps codegenReadyCompute list rich_list pred_set
  stackPlanGen cfgAnalysisProps removeUnusedSsaProofs

Theorem analyzed_output_live_point_to_after:
  !fn d bb j v p pb k.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\ MEM v (EL j bb.bb_instructions).inst_outputs /\
    fn_dominates fn d p /\ lookup_block p fn.fn_blocks = SOME pb /\
    LENGTH (collect_phis pb.bb_instructions) <= k /\ k <= LENGTH pb.bb_instructions /\
    (d = p ==> j < k) /\
    MEM v (live_vars_at (liveness_analyze fn) p k) ==>
    MEM v (live_vars_at (liveness_analyze fn) d (j+1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  drule_all dominates_analyzed_path_no_revisit >> strip_tac >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
  Cases_on `d = p`
  >- (gvs[] >>
      drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
      disch_then (qspecl_then [`d`, `bb`, `j+1`, `k`, `v`] mp_tac) >>
      simp[] >> disch_then irule >> simp[] >>
      rpt strip_tac >> gvs[inst_defs_def] >>
      `j < LENGTH bb.bb_instructions /\ k' < LENGTH bb.bb_instructions` by decide_tac >>
      `k' = j` by metis_tac[ssa_output_position_unique] >> decide_tac) >>
  suspend "different_blocks"
QED

Resume analyzed_output_live_point_to_after[different_blocks]:
  `tail <> []` by (Cases_on `tail` >> gvs[]) >>
  `?pre. tail = pre ++ [p]` by
    (qexists_tac `FRONT tail` >>
     `LAST tail = p` by (Cases_on `tail` >> gvs[]) >>
     metis_tac[APPEND_FRONT_LAST]) >>
  gvs[] >>
  `is_fn_path fn (SNOC p (d::pre))` by simp[SNOC_APPEND] >>
  drule removeUnusedSsaProofsTheory.is_fn_path_init >> strip_tac >>
  drule removeUnusedSsaProofsTheory.is_fn_path_last_edge >> simp[] >> strip_tac >>
  `EVERY (\inst. ~MEM v (inst_defs inst)) pb.bb_instructions` by
    (simp[EVERY_EL, inst_defs_def] >> rpt strip_tac >>
     `p = d` by metis_tac[ssa_output_position_unique] >> gvs[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) p
      (LENGTH (collect_phis pb.bb_instructions)))` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     disch_then (qspecl_then [`p`, `pb`, `LENGTH (collect_phis pb.bb_instructions)`, `k`, `v`] mp_tac) >>
     simp[] >> disch_then irule >> gvs[EVERY_EL]) >>
  `EVERY (phi_block_ready (liveness_analyze fn)) fn.fn_blocks` by
    (`phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
     fs[phi_operands_ready_def] >>
     gvs[EVERY_MEM] >> qx_gen_tac `b` >> strip_tac >>
     qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> NULL _`
       (qspec_then `b` mp_tac) >> simp[] >>
     Cases_on `collect_phis b.bb_instructions` >>
     simp[phi_block_ready_def, phi_uses_disjoint_def]) >>
  `pb.bb_label = p` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM v (input_vars_from (LAST (d::pre)) pb.bb_instructions
      (live_vars_at (liveness_analyze fn) p 0))` by
    (irule analyzed_ready_phi_live_through_edge >> simp[] >>
     reverse conj_tac
     >- (fs[EVERY_MEM] >> first_x_assum irule >>
         metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
     qspec_then `pb.bb_instructions` strip_assume_tac collect_phis_prefix >>
     qpat_x_assum `EVERY (\inst. ~MEM v (inst_defs inst)) pb.bb_instructions` mp_tac >>
     qpat_x_assum `pb.bb_instructions = _` (fn th => rewrite_tac[Once th, EVERY_APPEND]) >>
     simp[]) >>
  `EVERY (\lbl. cfg_reachable_of (cfg_analyze fn) lbl /\
      MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
      ?b. lookup_block lbl fn.fn_blocks = SOME b) (d::pre)` by
    (simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `cfg_reachable_of (cfg_analyze fn) (LAST (d::pre)) /\
   ?eb. lookup_block (LAST (d::pre)) fn.fn_blocks = SOME eb` by
    (qpat_assum `EVERY _ (d::pre)`
       (mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `LAST (d::pre)` mp_tac) >>
     simp[LAST_MEM]) >>
  `MEM p (cfg_succs_of (cfg_analyze fn) (LAST (d::pre)))` by
    metis_tac[fn_cfg_edge_cfg_analyze] >>
  `MEM v (live_vars_at (liveness_analyze fn) (LAST (d::pre))
      (LENGTH eb.bb_instructions))` by
    (drule_all analyzed_live_out_edge_subset >>
     simp[SUBSET_DEF] >> disch_then irule >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) d (LENGTH bb.bb_instructions))` by
    (irule analyzed_live_backward_no_kill_path >> simp[] >>
     qexistsl_tac [`eb`, `pre`] >> simp[] >>
     simp[EVERY_MEM] >> reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
     qx_gen_tac `lbl` >> strip_tac >>
     qx_gen_tac `b` >> strip_tac >> conj_tac
     >- metis_tac[venomExecPropsTheory.lookup_block_MEM, EVERY_MEM] >>
     `lbl <> d` by metis_tac[] >>
     simp[inst_defs_def] >> rpt strip_tac >>
     qpat_x_assum `MEM inst b.bb_instructions` mp_tac >>
     pure_rewrite_tac[MEM_EL] >> strip_tac >> gvs[] >>
     `lbl = d` by metis_tac[ssa_output_position_unique] >> gvs[]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
  disch_then (qspecl_then [`d`, `bb`, `j+1`, `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[inst_defs_def] >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  `k' = j` by metis_tac[ssa_output_position_unique] >> decide_tac
QED

Finalise analyzed_output_live_point_to_after
