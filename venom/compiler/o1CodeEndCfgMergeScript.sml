(* Whole-merge observations retain the concrete payload of the very same
   instruction, rather than erasing it through frame_sim. *)
Theory o1CodeEndCfgMerge
Ancestors
  o1CodeEndCfgBoundary simplifyCfgMergeSemantics simplifyCfgMergeClosure
  simplifyCfgFramePrefixes simplifyCfgFragments o1PassLift

Theorem scfg_merge_frame_observation:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  frame_reach C (scfg_chain fn a b) s0 i t /\ i.inst_opcode <> PHI ==>
  ?s. frame_reach C fn s0 i s /\ scfg_payload s t /\
      mem_corr i s i t /\ call_corr i s i t
Proof
  strip_tac >>
  `wf_function (scfg_chain fn a b)` by metis_tac[scfg_chain_wf] >>
  drule_all scfg_frame_reach_decompose >>
  disch_then (qx_choosel_then [`s`, `bb`, `v`, `e`] strip_assume_tac) >>
  `scfg_chain_exit a b s0 s0` by metis_tac[scfg_chain_initial_exit] >>
  `~s0.vs_halted` by fs[fn_entry_state_def] >>
  `?u. scfg_bprefix C fn s0 u /\ ~u.vs_halted /\ scfg_chain_exit a b u s` by
    (irule scfg_chain_bprefix_backward >>
     goal_assum (drule_at Any) >> simp[scfg_bprefix_rules] >>
     conj_tac >- (qexists_tac `s0` >> simp[scfg_bprefix_rules]) >>
     qexists_tac `s0` >> simp[]) >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  drule_all scfg_chain_rooted_observation >> simp[]
QED
