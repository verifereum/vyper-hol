Theory concretizeLayoutCompletedJump
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutParameterRoots
  frameRelocationValues concretizeLayoutScopedRun concretizeLayoutLocalJump
  concretizeLayoutRunState frameFiniteExecution frameJointTransition
  frameRelocationLocal frameRelocationEnvironment concretizeLayoutReaderContext
  concretizeLayoutSupplement ptrDiscipline venomExecSemantics venomState

(* A local view, NOT a sampled trace configuration.  The old ghosts, origin
   and demand cursor are retained; only the source control state is replaced.
   In particular this view must never be supplied to ordinary_trace. *)
Definition layout_jump_view_def:
  layout_jump_view a post =
    a with <|lop_pending := F;
      lop_config := case a.lop_config of
        JointConfig stk PG G tn fn inst s oms om hs h =>
          JointConfig stk PG G tn fn inst post oms om hs h|>
End

(* Completion is an endpoint of the old block, not an instruction entry.
   No OriginOrdinary event or successor PHI is asserted here. *)
Definition layout_completed_jump_def:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost <=>
    ~a.lop_pending /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q a s t /\
    get_instruction a.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
    get_instruction a.lop_origin.lbo_target t.vs_inst_idx = SOME j /\
    is_terminator inst.inst_opcode /\ is_terminator j.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ j.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK post /\ step_inst_base j t = OK tpost /\
    ~post.vs_halted /\ ~tpost.vs_halted /\
    ?lbl. post = jump_to lbl s /\ tpost = jump_to lbl t
End

Theorem layout_jump_view_indices:
  (layout_jump_view a post).lop_origin = a.lop_origin /\
  (layout_jump_view a post).lop_cursor = a.lop_cursor /\
  (layout_jump_view a post).lop_ids = a.lop_ids /\
  (layout_jump_view a post).lop_anns = a.lop_anns /\
  (layout_jump_view a post).lop_target_taint = a.lop_target_taint /\
  ~(layout_jump_view a post).lop_pending
Proof
  simp[layout_jump_view_def]
QED

Theorem layout_jump_view_state:
  ~a.lop_pending /\ layout_ordinary_state D lo C' q0 es qs a s t ==>
  layout_ordinary_state D lo C' q0 es qs
    (layout_jump_view a (jump_to lbl s)) (jump_to lbl s) (jump_to lbl t)
Proof
  Cases_on `a.lop_config` >>
  simp[layout_ordinary_state_def, layout_jump_view_def] >> strip_tac >>
  gvs[] >>
  simp[parameter_roots_def, jump_to_def, local_rel_def,
    variable_domains_def, variables_agree_on_def, local_values_def,
    lookup_var_def, concretize_local_obs_def, dead_result_rel_def,
    relocation_env_def, relocation_reader_context_def,
    concretize_supplement_def] >>
  gvs[parameter_roots_def, local_rel_def, variable_domains_def,
    variables_agree_on_def, local_values_def, lookup_var_def,
    concretize_local_obs_def, dead_result_rel_def, relocation_env_def,
    relocation_reader_context_def, concretize_supplement_def]
QED

Theorem layout_completed_jump_local:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost ==>
  layout_ordinary_state D lo C' q0 es qs (layout_jump_view a post) post tpost
Proof
  simp[layout_completed_jump_def] >> strip_tac >>
  gvs[] >> irule layout_jump_view_state >>
  fs[layout_ordinary_entry_def]
QED

(* The block result retains a.lop_origin, including its original entry.
   These are the actual block_term constructors consumed by finite_run. *)
Theorem layout_completed_jump_blocks:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost ==>
  finite_block C a.lop_origin.lbo_source s (OK post) /\
  finite_block C' a.lop_origin.lbo_target t (OK tpost)
Proof
  simp[layout_completed_jump_def] >> strip_tac >>
  `finite_step C inst s (OK post)` by
    (irule finite_step_base >> simp[]) >>
  `finite_step C' j t (OK tpost)` by
    (irule finite_step_base >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `finite_step C' _ _ _` kall_tac >>
      drule_all finite_step_block_term >> simp[]) >>
  drule_all finite_step_block_term >> simp[]
QED

(* Exact consumer boundary.  Event availability is a continuation obligation,
   not part of block completion.  Existing layout_run_block_state owns PHI
   relocation, resolved_entry, target taint and successor demand transport. *)
Theorem layout_completed_jump_continue:
  layout_completed_jump D lo vs0 C C' q0 es qs q a inst j s t post tpost /\
  vs0.vs_allocas = FEMPTY /\
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
    EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) /\
  post.vs_current_bb = tpost.vs_current_bb /\
  post.vs_prev_bb = tpost.vs_prev_bb ==>
  ?b. b.lop_origin = a.lop_origin /\
    b.lop_cursor = SUC a.lop_cursor /\
    layout_scoped_run D lo vs0 C C' q0 es qs q (INL b) fn
      (concretize_function_with_positions positions fn) post tpost
Proof
  strip_tac >>
  drule layout_completed_jump_local >> strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q a s` by
    fs[layout_completed_jump_def, layout_ordinary_entry_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_jump_view_def, layout_ordinary_state_def] >> strip_tac >>
  drule_all layout_run_block_state >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  `enters_block fn post sentry` by
    (fs[joint_transition_block_iff] >> metis_tac[]) >>
  qexists `b` >> simp[] >>
  irule layout_scoped_run_intro >> qexistsl [`b`, `sentry`, `tentry`] >> simp[]
QED

val _ = export_theory();
