Theory bodyPtrBopInRuntimePost
Ancestors bodyPtrBopInLoopContract exprSimPtrProps stmtSimAppendStorageCompose
  bodyPtrBopInCompose bodyPtrDefs exprSimWordArgs stateFrame venomState
  ptrDiscipline compileEnv exprLoweringProps

(* Two jumps erase the entire incoming cursor, including the predecessor.
   stmt_state_rel is invariant under each jump. *)
Theorem membership_runtime_state_rel:
  membership_loop_frame sm G tn s G' tn' t /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sm ==>
  stmt_state_rel ctx fn cenv cx ee t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee (s with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_reserved_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `sm` >> fs[membership_loop_frame_def, state_frame_def, lookup_var_def]) >>
  `jump_to "" (jump_to "" t) =
   jump_to "" (jump_to "" (s with vs_vars := t.vs_vars))` by
    (fs[membership_loop_frame_def] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[jump_to_def]) >>
  `stmt_state_rel ctx fn cenv cx ee (jump_to "" (jump_to "" t))`
    suffices_by simp[stmt_state_rel_jump_to] >>
  asm_rewrite_tac[] >> simp[stmt_state_rel_jump_to]
QED

Theorem membership_runtime_readonly_frames:
  membership_loop_frame sm G tn s G' tn' t /\
  stmt_state_rel ctx fn cenv cx ee s /\ ghost_inv d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  wb_frame cenv es sa s0 s /\ sa.cs_next_var <= sm.cs_next_var ==>
  stmt_state_rel ctx fn cenv cx ee t /\ ghost_inv d cenv cx ee G' tn' t /\
  ghost_kept cenv ee sm G tn s G' tn' /\ wb_frame cenv es sa s0 t
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    (fs[membership_loop_frame_def] >>
     qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- metis_tac[membership_runtime_state_rel] >>
  conj_tac
  >- (irule ghost_inv_fresh_frame >>
      goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
      qexists_tac `sm` >> fs[membership_loop_frame_def]) >>
  conj_tac >- metis_tac[membership_loop_frame_ghost_kept] >>
  irule wb_frame_readonly_tail >>
  goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  qexists_tac `sm` >> fs[membership_loop_frame_def]
QED
