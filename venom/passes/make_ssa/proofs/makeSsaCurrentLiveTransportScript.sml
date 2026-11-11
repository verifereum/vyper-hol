Theory makeSsaCurrentLiveTransport
Ancestors
  makeSsaCurrentSelectedLive makeSsaCurrentDefs makeSsaCurrentDemandDominance
  livenessDefs livenessAnalysisProps livenessLocalProofs dfAnalyzeDefs venomInst venomWf
  venomExecProps list alist makeSsaCurrentAnalysis cfgAnalysisProps cfgWf relation livenessProofs

Theorem current_after_phis_lookup:
  !bbs l bb live. lookup_block l bbs = SOME bb /\ bb.bb_instructions <> [] ==>
  ALOOKUP (current_live_in_after_phis live bbs) l =
    SOME (live_vars_at live l (LENGTH (collect_phis bb.bb_instructions)))
Proof
  Induct >> simp[lookup_block_def, FIND_thm, current_live_in_after_phis_def] >>
  rpt gen_tac >> Cases_on `h.bb_label = l` >> simp[]
  >- (strip_tac >> gvs[] >> Cases_on `bb.bb_instructions` >> gvs[] >>
      Cases_on `h.inst_opcode = PHI` >> simp[collect_phis_def]) >>
  metis_tac[lookup_block_def]
QED

Theorem current_no_leading_phi_cut:
  !bbs l bb. ~blocks_have_leading_phi bbs /\ lookup_block l bbs = SOME bb ==>
  collect_phis bb.bb_instructions = []
Proof
  Induct >> simp[blocks_have_leading_phi_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_instructions` >> simp[collect_phis_def] >>
  Cases_on `h.bb_label = l` >> simp[] >> rpt strip_tac >>
  gvs[collect_phis_def] >> metis_tac[lookup_block_def]
QED

Theorem current_selected_live_iff:
  wf_function fn /\ lookup_block l fn.fn_blocks = SOME bb ==>
  ((?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) l = SOME vs /\ MEM v vs) <=>
   MEM v (live_vars_at (liveness_analyze fn) l
     (LENGTH (collect_phis bb.bb_instructions))))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = l` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb.bb_instructions <> []` by
    metis_tac[wf_function_def, bb_well_formed_def] >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks`
  >- (drule_all current_after_phis_lookup >>
      disch_then (qspec_then `liveness_analyze fn` assume_tac) >>
      simp[select_current_live_in_def]) >>
  `collect_phis bb.bb_instructions = []` by metis_tac[current_no_leading_phi_cut] >>
  `MEM l (fn_labels fn)` by (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  simp[select_current_live_in_def, ALOOKUP_current_query_map,
       liveness_analyze_def, liveness_recompute_boundary_entry]
QED

Theorem current_all_labels_dfs_pre:
  wf_function fn /\ all_reachable fn /\ MEM l (fn_labels fn) ==>
  MEM l (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule cfg_analyze_reachable_sets >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) l` by
    metis_tac[current_all_labels_reachable] >>
  fs[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem current_live_cut_to_pred_exit:
  wf_function fn /\ all_reachable fn /\ fn_cfg_edge fn a b /\
  lookup_block a fn.fn_blocks = SOME ab /\
  lookup_block b fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) b
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs inst.inst_operands))) ==>
  MEM v (live_vars_at (liveness_analyze fn) a (LENGTH ab.bb_instructions))
Proof
  strip_tac >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM a (cfg_analyze fn).cfg_dfs_pre /\
   MEM b (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[current_all_labels_dfs_pre] >>
  `MEM v (live_vars_at (liveness_analyze fn) b 0)` by
    (drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
     simp[] >> qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
     simp[current_collect_phis_length]) >>
  drule live_vars_at_cross_block >> simp[] >> disch_then irule >>
  simp[GSYM current_cfg_edge_succs] >>
  qexistsl_tac [`bb`, `b`] >> simp[]
QED

Theorem current_live_exit_to_cut:
  wf_function fn /\ all_reachable fn /\
  lookup_block a fn.fn_blocks = SOME ab /\
  MEM v (live_vars_at (liveness_analyze fn) a (LENGTH ab.bb_instructions)) /\
  (!k. LENGTH (collect_phis ab.bb_instructions) <= k /\
       k < LENGTH ab.bb_instructions ==>
       ~MEM v (inst_defs (EL k ab.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) a
    (LENGTH (collect_phis ab.bb_instructions)))
Proof
  strip_tac >>
  `MEM a (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM a (cfg_analyze fn).cfg_dfs_pre` by metis_tac[current_all_labels_dfs_pre] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
  simp[] >> qexists_tac `LENGTH ab.bb_instructions` >>
  simp[current_collect_phis_length]
QED

Theorem current_selected_live_edge:
  wf_function fn /\ all_reachable fn /\ fn_cfg_edge fn a b /\
  lookup_block a fn.fn_blocks = SOME ab /\
  lookup_block b fn.fn_blocks = SOME bb /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs inst.inst_operands))) /\
  (!k. LENGTH (collect_phis ab.bb_instructions) <= k /\
       k < LENGTH ab.bb_instructions ==>
       ~MEM v (inst_defs (EL k ab.bb_instructions))) ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs
Proof
  strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) b
    (LENGTH (collect_phis bb.bb_instructions)))` by
    metis_tac[current_selected_live_iff] >>
  `MEM v (live_vars_at (liveness_analyze fn) a (LENGTH ab.bb_instructions))` by
    metis_tac[current_live_cut_to_pred_exit] >>
  metis_tac[current_live_exit_to_cut, current_selected_live_iff]
QED

(* Each edge constrains only the source suffix and destination prefix.
   Consequently a route constrains whole interior blocks, but allows earlier
   definitions in its initial block and later definitions in its final block. *)
Definition current_live_route_edge_def:
  current_live_route_edge fn v a b <=>
    fn_cfg_edge fn a b /\
    ?ab bb. lookup_block a fn.fn_blocks = SOME ab /\
      lookup_block b fn.fn_blocks = SOME bb /\
      (!k. LENGTH (collect_phis ab.bb_instructions) <= k /\
           k < LENGTH ab.bb_instructions ==>
           ~MEM v (inst_defs (EL k ab.bb_instructions))) /\
      (!k. k < LENGTH (collect_phis bb.bb_instructions) ==>
           ~MEM v (inst_defs (EL k bb.bb_instructions))) /\
      (!inst. MEM inst (collect_phis bb.bb_instructions) ==>
        ~MEM v (MAP SND (phi_pairs inst.inst_operands)))
End

Theorem current_selected_live_route_step:
  wf_function fn /\ all_reachable fn /\ current_live_route_edge fn v a b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs
Proof
  simp[current_live_route_edge_def] >> strip_tac >>
  irule current_selected_live_edge >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
  qexists_tac `b` >> simp[] >> metis_tac[]
QED

Theorem current_selected_live_route:
  !ls a b. wf_function fn /\ all_reachable fn /\
  LRC (current_live_route_edge fn v) ls a b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) a = SOME vs /\ MEM v vs
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[current_selected_live_route_step]
QED

Theorem current_live_route_cfg:
  !ls a b. LRC (current_live_route_edge fn v) ls a b ==>
    LRC (fn_cfg_edge fn) ls a b
Proof
  Induct >> simp[LRC_def, current_live_route_edge_def] >> metis_tac[]
QED
