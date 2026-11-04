(* Global frame observation transport for PHI fixup. *)
Theory simplifyCfgFixupFrames
Ancestors
  simplifyCfgFramePrefixes simplifyCfgFixupRuns simplifyCfgFixupPrefixes
  simplifyCfgFixupSemantics simplifyCfgFragments
  simplifyCfgDefs o1PassLift
  simplifyCfgStruct

Theorem scfg_fix_all_phis_frame_sim:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  (!b. MEM b fn.fn_blocks ==> fn_reachable fn b.bb_label) ==>
  frame_sim L C C fn (fix_all_phis fn)
Proof
  strip_tac >> simp[frame_sim_def] >> rpt strip_tac >>
  `wf_function (fix_all_phis fn)` by metis_tac[fix_all_phis_wf] >>
  drule_all scfg_frame_reach_decompose >> strip_tac >>
  `scfg_bprefix C fn s0 s` by
    (irule scfg_fix_all_phis_bprefix_backward >> simp[] >>
     metis_tac[scfg_bprefix_rules]) >>
  qpat_x_assum `lookup_block _ _ = _` mp_tac >>
  rewrite_tac[scfg_fix_all_phis_lookup] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  strip_tac >> gvs[] >>
  irule scfg_rooted_fix_phis_observe >> simp[] >> metis_tac[]
QED
