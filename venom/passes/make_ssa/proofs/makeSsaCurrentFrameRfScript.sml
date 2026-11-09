(*
 * The revert-forward half of MakeSSA's frame simulation: a state of an
 * output frame that touches memory away from a revert-forward copy
 * corresponds to one of the input frame that is not at a revert-forward
 * copy either.  o1PassLift needs it, beside frame_sim, to carry memory
 * facts that exempt revert forwarding (raw_mem_ok, lowered_mem_fact).
 *)
Theory makeSsaCurrentFrameRf
Ancestors
  o1PassLift makeSsaDefs venomWf cfgWf venomInst irSupply
  unitShapeDefs o1PassContract o1FrameLockstep makeSsaCurrentLockstep
  makeSsaCurrentLockstepRf makeSsaCurrentRevertForward

Theorem make_ssa_current_fn_frame_sim_rf:
  ctx_bisim C C' /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  frame_sim_rf L C C' fn fn'
Proof
  strip_tac >>
  drule_all make_ssa_current_fn_frame_lockstep >>
  disch_then (qspec_then `L` mp_tac) >>
  rw[frame_lockstep_def] >>
  irule lockstep_frame_sim_rf >>
  qexistsl [`R`, `make_ssa_pos fn fn'`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[make_ssa_pos_def] >>
      drule_all make_ssa_current_fn_revert_forward_at >> simp[]) >>
  rpt strip_tac >> irule frame_reach_lockstep_rel >> metis_tac[]
QED
