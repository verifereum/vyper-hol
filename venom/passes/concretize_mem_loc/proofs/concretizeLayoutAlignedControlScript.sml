Theory concretizeLayoutAlignedControl
Ancestors frameControlAgreement concretizeLayoutCompletedJump
  concretizeLayoutPhaseOrigin concretizeLayoutCallControl

(* Pending entries use the same companion relation: normalization only
   changes the instruction index and leaves both control labels untouched. *)
Definition layout_aligned_state_def:
  layout_aligned_state D lo C' q0 es qs a s t <=>
    layout_ordinary_state D lo C' q0 es qs a s t /\ control_agree s t
End

Definition layout_aligned_entry_def:
  layout_aligned_entry D lo vs0 C C' q0 es qs q a s t <=>
    layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t /\ control_agree s t
End

Theorem layout_aligned_entry_elim:
  layout_aligned_entry D lo vs0 C C' q0 es qs q a s t ==>
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t /\
  layout_aligned_state D lo C' q0 es qs a s t
Proof
  simp[layout_aligned_entry_def, layout_aligned_state_def,
    layout_ordinary_entry_def]
QED

Theorem control_agree_normalize[simp]:
  control_agree (layout_phase_normalize p s) (layout_phase_normalize p' t) <=>
  control_agree s t
Proof
  Cases_on `p` >> Cases_on `p'` >>
  simp[layout_phase_normalize_def, control_agree_def]
QED

Theorem layout_aligned_step:
  layout_aligned_entry D lo vs0 C C' q0 es qs q a s t /\
  step_inst fuel C inst s = OK post /\
  step_inst fuel' C' inst' t = OK post' /\
  ~is_terminator inst.inst_opcode /\ ~is_terminator inst'.inst_opcode /\
  layout_ordinary_entry D lo vs0 C C' q0 es qs q b post post' ==>
  layout_aligned_entry D lo vs0 C C' q0 es qs q b post post'
Proof
  simp[layout_aligned_entry_def] >> metis_tac[control_agree_step]
QED

Theorem layout_aligned_jump_state:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost /\
  control_agree s t ==>
  layout_aligned_state D lo C' q0 es qs (layout_jump_view a post) post tpost
Proof
  strip_tac >> simp[layout_aligned_state_def] >>
  conj_tac >- metis_tac[layout_completed_jump_local] >>
  fs[layout_completed_jump_def] >> gvs[] >> irule control_agree_jump >> simp[]
QED

(* No new post-control hypotheses: agreement comes from the saved entry.
   The OriginBlock edge remains explicit, supplied by selected decoration. *)
Theorem layout_aligned_completed_jump_continue:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost /\
  control_agree s t /\ vs0.vs_allocas = FEMPTY /\
  a.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::saved /\
  a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) /\
  EL (SUC a.lop_cursor) (q0::qs) =
    JointConfig stk PG G' tn' fn inst' sentry oms om' hs h' /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post))
    (JointConfig stk PG G' tn' fn inst' sentry oms om' hs h') /\
  EVERY bb_well_formed fn.fn_blocks /\
  (!bb. MEM bb fn.fn_blocks ==>
    EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) ==>
  ?b. b.lop_origin = a.lop_origin /\
    b.lop_cursor = SUC a.lop_cursor /\
    layout_scoped_run D lo vs0 C C' q0 es qs q (INL b) fn
      (concretize_function_with_positions positions fn) post tpost
Proof
  strip_tac >>
  `control_agree post tpost` by
    (drule_all layout_aligned_jump_state >> simp[layout_aligned_state_def]) >>
  fs[control_agree_def] >>
  drule layout_completed_jump_continue >> simp[]
QED

Theorem layout_aligned_caller_restore:
  control_agree caller caller' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME post /\
  bind_outputs outs' ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' callee')) = SOME post' ==>
  control_agree (post with vs_inst_idx := SUC caller.vs_inst_idx)
    (post' with vs_inst_idx := SUC caller'.vs_inst_idx)
Proof
  strip_tac >> simp[] >> irule control_agree_bind_outputs >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  irule control_agree_restore >> simp[]
QED

val _ = export_theory();
