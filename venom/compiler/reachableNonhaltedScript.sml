(* Nonhaltedness for active frames and their suspended callers. *)
Theory reachableNonhalted
Ancestors
  reachableFnSim ptrDiscipline contextCodegenRel venomExecSemantics
  venomState venomExecProofs venomStepProps list

Theorem frame_reachable_nonhalted_stack:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    (~vs.vs_halted ==>
      ~s.vs_halted /\ EVERY (\f. ~f.cf_state.vs_halted) stk)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[enters_block_def] >>
      drule eval_phis_preserves_halted >> simp[])
  >- (rpt strip_tac >> drule step_inst_ok_halted >> gvs[])
  >- (rpt strip_tac >> gvs[enters_block_def] >>
      drule eval_phis_preserves_halted >> simp[])
  >- (rpt strip_tac >> gvs[enters_block_def] >>
      drule eval_phis_preserves_halted >>
      gvs[setup_callee_def, AllCaseEqs()])
  >> rpt strip_tac >> gvs[] >>
  drule bind_outputs_ok_halted >>
  simp[merge_callee_state_def]
QED

Theorem frame_reachable_not_halted:
  frame_reachable vs C stk PG G tn fn inst s /\ ~vs.vs_halted ==>
  ~s.vs_halted
Proof
  metis_tac[frame_reachable_nonhalted_stack]
QED

Theorem block_reach_not_halted:
  block_reach vs C stk PG G tn fn s /\ ~vs.vs_halted /\
  enters_block fn s s1 /\ active_inst fn inst s1 ==>
  ~s.vs_halted
Proof
  rw[block_reach_def] >>
  `~s1.vs_halted` by metis_tac[frame_reachable_not_halted] >>
  gvs[enters_block_def] >> drule eval_phis_preserves_halted >> simp[]
QED
