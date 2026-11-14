(* Guarded bypass reflects ordinary observations without erasing payload. *)
Theory o1CodeEndCfgBypass
Ancestors
  o1CodeEndCfgBoundary simplifyCfgBypassSemantics simplifyCfgBypassPrefix
  simplifyCfgBypassShape simplifyCfgBypassClosure simplifyCfgBypassEntry
  simplifyCfgControl simplifyCfgSimTools
  simplifyCfgFragments simplifyCfgStaticInterface venomExecProps o1PassLift

Theorem scfg_bypass_frame_observation:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' /\
  fn_entry_state fn s0 /\ frame_reach C' fn' s0 j t /\
  j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode ==>
  ?s. frame_reach C fn s0 j s /\ scfg_payload s t /\
      mem_corr j s j t /\ call_corr j s j t
Proof
  strip_tac >>
  `scfg_bypass_aligned a b s0 s0` by
    metis_tac[scfg_bypass_initial_aligned] >>
  drule_all scfg_bypass_rooted_observe >>
  disch_then (qx_choosel_then [`s`, `i`] strip_assume_tac) >>
  `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b))
     s.vs_current_bb i = i` by
    (irule scfg_bypass_image_ordinary_inv >> metis_tac[]) >>
  `scfg_payload s t` by
    fs[scfg_bypass_aligned_def, scfg_payload_def, scfg_ctrl_def] >>
  `inst_wf i` by
    metis_tac[frame_reach_active, active_inst_wf, scfg_bypass_old_static,
              scfg_static_inst_wf] >>
  gvs[] >> qexists_tac `s` >>
  metis_tac[scfg_payload_mem_corr, scfg_payload_call_corr]
QED
