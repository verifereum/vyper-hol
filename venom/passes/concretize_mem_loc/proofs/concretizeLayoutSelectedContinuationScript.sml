Theory concretizeLayoutSelectedContinuation
Ancestors concretizeLayoutAlignedControl frameSelectedDecoration
  concretizeLayoutDecoratedBlockContinuation concretizeLayoutRunState
  concretizeLayoutCompletedJump frameJointTransition frameControlAgreement
  concretizeLayoutPhaseOrigin arithmetic

(* The selected run_next supplies the actual edge and following derivation.
   Completion itself remains unsampled, and the ambient trace is unchanged. *)
Theorem layout_selected_jump_entry:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost /\
  control_agree s t /\ vs0.vs_allocas = FEMPTY /\
  a.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::saved /\
  es = MAP FST path /\ qs = MAP SND path /\
  a.lop_cursor = n + LENGTH wb /\
  selected_segment C q0 path n qb
    (wb ++ ([(SOME (OriginBlock fuel post),qn)] ++ wr)) qe /\
  decorated_block C bb phi (OK post) qb n wb a.lop_config db /\
  joint_transition C a.lop_config (SOME (OriginBlock fuel post)) qn /\
  qn = JointConfig stk PG G' tn' fn inst' sentry oms om' hs h' /\
  decorated_run C fn post r qn (n + LENGTH wb + 1) wr qe dr /\
  EVERY bb_well_formed fn.fn_blocks /\
  (!bb. MEM bb fn.fn_blocks ==>
    EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) ==>
  selected_run C q0 path fn post r qn (SUC a.lop_cursor) wr qe dr /\
  ?tentry b.
    enters_block (concretize_function_with_positions positions fn) tpost tentry /\
    b.lop_cursor = SUC a.lop_cursor /\ b.lop_origin = a.lop_origin /\
    layout_ordinary_trace vs0 C q0 es qs q b sentry /\
    layout_aligned_state D lo C' q0 es qs b sentry tentry
Proof
  strip_tac >>
  drule_all selected_run_next_children >> strip_tac >>
  `control_agree post tpost` by
    (drule_all layout_aligned_jump_state >> simp[layout_aligned_state_def]) >>
  conj_tac >- gvs[ADD1] >>
  `layout_ordinary_trace vs0 C q0 es qs q a s` by
    fs[layout_completed_jump_def, layout_ordinary_entry_def] >>
  drule layout_completed_jump_local >>
  simp[layout_jump_view_def, layout_ordinary_state_def] >> strip_tac >>
  `EL (SUC a.lop_cursor) (q0::qs) =
    JointConfig stk PG G' tn' fn inst' sentry oms om' hs h'` by
      metis_tac[ADD1, ADD_ASSOC] >>
  `a.lop_cursor < LENGTH es` by gvs[] >>
  fs[control_agree_def] >>
  qpat_x_assum `es = MAP FST path` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `qs = MAP SND path` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `a.lop_cursor = n + LENGTH wb` (SUBST_ALL_TAC o SYM) >>
  gvs[] >>
  drule_all (SRULE [] layout_run_block_state) >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  `enters_block fn post sentry` by
    (fs[joint_transition_block_iff] >> metis_tac[]) >>
  qexistsl [`tentry`, `b`] >> simp[layout_aligned_state_def] >>
  irule control_agree_enters_block >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[control_agree_def]
QED

val _ = export_theory();
