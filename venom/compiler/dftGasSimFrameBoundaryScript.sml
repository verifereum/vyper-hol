Theory dftGasSimFrameBoundary
Ancestors
  dftGasSimDominance dftGasSimInvariant dftGasSimSuccessor dftGasOracleDefs
  dftRunRel venomExecProofs venomExecProps venomExecSemantics venomWf
  sccpCorrectnessProofs venomInst venomState list

Theorem ev_block_entry_frame_inv:
  wf_function fn /\ MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  ev_block orc p d fuel C bb
    (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
  strict_dom_vars_defined fn s /\ fn_reachable fn s.vs_current_bb /\
  ctx_labels_bound C s.vs_labels /\ ~s.vs_call_ctx.cc_static ==>
  strict_dom_vars_defined fn t /\ fn_reachable fn t.vs_current_bb /\
  ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static
Proof
  strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  `strict_dom_vars_defined fn t` by
    (irule ev_strict_dom_vars_defined_block_entry >> metis_tac[]) >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule ev_block_current_bb_in_succs >>
     conj_tac >- simp[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `ev_block _ _ _ _ _ _ _ = OK _`)) >>
     simp[phi_prefix_length_le]) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `t.vs_labels = s.vs_labels` by
    (drule ev_block_labels >> drule eval_phis_preserves_labels >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (drule ev_block_call_ctx >> drule dft_eval_phis_call_ctx >> simp[]) >>
  metis_tac[fn_reachable_step]
QED
