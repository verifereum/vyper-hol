Theory concretizeLayoutEntryFlags
Ancestors concretizeLayoutPhaseOrigin frameJointTrace frameJointTransition
  frameOriginHistory frameOriginReachable ptrDiscipline venomStepProps
  venomExecProofs venomExecSemantics venomState contextCodegenRel list

(* Saved callers retain their own flag; callee return restores that flag. *)
Theorem layout_reachable_frame_flags:
  !vs0 C stk PG G tn fn inst s.
    frame_reachable vs0 C stk PG G tn fn inst s ==>
    ~vs0.vs_halted ==>
    ~s.vs_halted /\ EVERY (\f. ~f.cf_state.vs_halted) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> fs[enters_block_def] >>
      drule eval_phis_preserves_halted >> gvs[])
  >- (rpt strip_tac >> drule step_inst_ok_halted >> gvs[])
  >- (rpt strip_tac >> fs[enters_block_def] >>
      drule eval_phis_preserves_halted >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      fs[enters_block_def, setup_callee_def, AllCaseEqs()] >>
      drule eval_phis_preserves_halted >> gvs[])
  >> rpt strip_tac >> gvs[] >>
  drule bind_outputs_ok_halted >>
  simp[merge_callee_state_def]
QED

Theorem layout_ordinary_entry_halted_agree:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t ==>
  s.vs_halted = t.vs_halted
Proof
  Cases_on `a.lop_config` >>
  simp[layout_ordinary_entry_def, layout_ordinary_state_def] >>
  rpt strip_tac >>
  fs[frameRelocationLocalTheory.local_rel_def,
     concretizeLayoutSupplementTheory.concretize_local_obs_def, dead_result_rel_def]
QED

Theorem layout_ordinary_entry_nonhalting:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t /\
  ~vs0.vs_halted ==>
  ~s.vs_halted /\ ~t.vs_halted
Proof
  strip_tac >>
  drule layout_ordinary_entry_halted_agree >> strip_tac >>
  Cases_on `a.lop_config` >>
  fs[layout_ordinary_entry_def, layout_ordinary_trace_def,
     layout_ordinary_state_def] >>
  drule joint_trace_prefix_reachable >>
  rewrite_tac[EVERY_EL] >> strip_tac >>
  qpat_x_assum `!n. _` (qspec_then `a.lop_cursor` mp_tac) >>
  simp[] >>
  simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  drule layout_reachable_frame_flags >>
  simp[layout_phase_normalize_def] >>
  Cases_on `a.lop_pending` >> gvs[]
QED

val _ = export_theory();
