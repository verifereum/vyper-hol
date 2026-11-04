Theory fnPlanLineagePath
Ancestors
  fnPlanLineagePhiActivation fnPlanLineageLiveness stackPlanGen livenessDefs
  livenessAnalysisProps cfgAnalysisProps removeUnusedProofs
  removeUnusedSsaProofs codegenReadyCompute

Theorem analyzed_ready_live_through_edge:
  !fn lbl bb pred pred_bb v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  EVERY (\inst. ~MEM v (inst_defs inst)) bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) /\
  cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions)))` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     disch_then (qspecl_then [`lbl`, `bb`, `LENGTH (collect_phis bb.bb_instructions)`,
       `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
     gvs[listTheory.EVERY_EL] >> metis_tac[]) >>
  `EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  drule_all analyzed_ready_phi_live_through_edge >>
  disch_then (qspec_then `pred` assume_tac) >>
  drule_all analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

(* Symbolic producer ledger (C3.2.2.21):
   - reachable_phi_incoming_live_out supplies the actual predecessor seed.
   - analyzed_ready_live_through_edge above transports an exit seed through
     a ready block with no definition of v, without any incoming-use seed.
   - Existing native path bridge: dominates_path_no_revisit in
     venom/passes/remove_unused/proofs/removeUnusedProofsScript.sml
     (lines 1734-1752) already proves, under wf_function fn and
     fn_dominates fn d p, existence of a native path d::tail ending at p
     with ~MEM d tail. It uses local rtc_to_is_fn_path,
     last_occurrence_split and is_fn_path_suffix. Do not duplicate it.
     Exported at its single definition site for reuse here, along with
     ssa_unique_var_defined_at; their proof dependencies stay local.
     The remaining strengthened interface must additionally supply vertex
     reachability, lookup witnesses and analyzed-CFG edge membership.
     Empty tail covers d=p.
   - SSA must identify the available definition with the prefix definition,
     and rule out v definitions in all tail blocks and after its head PHIs.
     Then induction on the path applies the edge boundary; at the head only
     propagate to LENGTH collect_phis, never across the defining PHI.
   - fn_cfg_edge must be converted to analyzed cfg_succs membership, with
     reachability/lookup facts for each path vertex. Existing remove-unused
     live_backward_along_path is not reusable: its remove_unused_phi_vars
     exclusion is precisely the incoming-alias situation at issue.
   These are explicit remaining symbolic proof obligations, not premises
   added to the frozen theorem or an assertion of global alias exclusion.
*)

Theorem dominates_analyzed_path_no_revisit:
  !fn d p.
    wf_function fn /\ fn_dominates fn d p ==>
    ?tail. is_fn_path fn (d::tail) /\ LAST (d::tail) = p /\
      ~MEM d tail /\
      EVERY (\lbl. fn_reachable fn lbl /\
        cfg_reachable_of (cfg_analyze fn) lbl /\
        MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
        ?bb. lookup_block lbl fn.fn_blocks = SOME bb) (d::tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dominates_path_no_revisit >> strip_tac >>
  qexists_tac `path` >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  `fn_reachable fn d` by
    metis_tac[fn_dominates_dom_reachable_compute] >>
  rewrite_tac[listTheory.EVERY_MEM] >> qx_gen_tac `lbl` >> strip_tac >>
  `fn_reachable fn lbl` by
    (irule is_fn_path_all_reachable >>
     qexists_tac `d::path` >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  metis_tac[fn_reachable_has_block]
QED
