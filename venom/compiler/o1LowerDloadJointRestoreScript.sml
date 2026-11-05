(* Complete local caller-frame restoration; no historical shared-state premise. *)
Theory o1LowerDloadJointRestore
Ancestors
  o1LowerDloadJointRelation o1LowerDloadRestore o1LowerDloadEnvironment
  o1LowerDloadJointAssign contextCodegenRel
  venomExecSemantics venomInstProofs1 venomState ptrDiscipline
  finite_map list pred_set

Theorem ld_bind_outputs_vars_only:
  bind_outputs outs vals s = SOME s1 ==>
  s1 = s with vs_vars := s1.vs_vars
Proof
  strip_tac >>
  `s1 with vs_vars := s.vs_vars = s with vs_vars := s.vs_vars` by
    (irule bind_outputs_preserves >>
     simp[update_var_def] >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED

Theorem ld_joint_control_merge_vars[local]:
  ld_joint_control u fn fn'
    ((merge_callee_state s c) with vs_vars := sv)
    ((merge_callee_state t d) with vs_vars := tv) <=>
  ld_joint_control u fn fn' s t
Proof
  simp[ld_joint_control_def, merge_callee_state_def]
QED

Theorem ld_joint_frame_return_restore:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv caller caller' /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME s1 ==>
  ?t1. bind_outputs outs vals (merge_callee_state caller' callee') = SOME t1 /\
    ld_joint_frame sites X lo owner older u fn fn'
      (DRESTRICT H (COMPL (set outs))) HP
      (DRESTRICT tv (COMPL (set outs))) s1 t1
Proof
  strip_tac >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  qabbrev_tac `tn = entry_taint with t_var := tv` >>
  drule_all ld_return_local_restore >>
  disch_then (qspec_then `callee'` strip_assume_tac) >>
  fs[Abbr `tn`] >>

  `s1 = (merge_callee_state caller callee) with vs_vars := s1.vs_vars` by
    (irule ld_bind_outputs_vars_only >> goal_assum drule) >>
  `t1 = (merge_callee_state caller' callee') with vs_vars := t1.vs_vars` by
    (irule ld_bind_outputs_vars_only >> goal_assum drule) >>
  `ld_joint_control u fn fn' s1 t1` by
    (qpat_x_assum `ld_joint_control _ _ _ _ _` mp_tac >>
     qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[ld_joint_control_merge_vars]) >>
  `ld_joint_allocas sites X owner fn t1` by
    (qpat_x_assum `ld_joint_allocas _ _ _ _ _` mp_tac >>
     qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[ld_joint_allocas_def, merge_callee_state_def] >> strip_tac >> simp[]) >>
  `ld_joint_local_fields s1 t1` by
    (qpat_x_assum `ld_joint_local_fields _ _` mp_tac >>
     qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[ld_joint_local_fields_def, merge_callee_state_def]) >>
  simp[ld_joint_frame_def] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  simp[merge_callee_state_def] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ld_joint_frame_return_next:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv caller caller' /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn callinst caller /\ callinst.inst_opcode = INVOKE /\
  bind_outputs callinst.inst_outputs vals (merge_callee_state caller callee) = SOME s1 /\
  active_inst fn next (s1 with vs_inst_idx := SUC caller.vs_inst_idx) ==>
  ?t1. bind_outputs callinst.inst_outputs vals
        (merge_callee_state caller' callee') = SOME t1 /\
    active_inst fn' callinst caller' /\
    ld_joint_frame sites X lo owner older u fn fn'
      (DRESTRICT H (COMPL (set callinst.inst_outputs))) HP
      (DRESTRICT tv (COMPL (set callinst.inst_outputs)))
      (s1 with vs_inst_idx := SUC caller.vs_inst_idx)
      (t1 with vs_inst_idx := SUC caller'.vs_inst_idx)
Proof
  strip_tac >>
  drule_all ld_joint_frame_return_restore >>
  disch_then (qspec_then `callee'` strip_assume_tac) >>
  `s1 = (merge_callee_state caller callee) with vs_vars := s1.vs_vars` by
    (irule ld_bind_outputs_vars_only >> goal_assum drule) >>
  `t1 = (merge_callee_state caller' callee') with vs_vars := t1.vs_vars` by
    (irule ld_bind_outputs_vars_only >> goal_assum drule) >>
  `active_inst fn next (caller with vs_inst_idx := SUC caller.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn next _` mp_tac >>
     qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[active_inst_def, merge_callee_state_def]) >>
  `ld_joint_control u fn fn' caller caller'` by fs[ld_joint_frame_def] >>
  `~MEM callinst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  `!st ca vars idx.
     ((merge_callee_state st ca with vs_vars := vars) with vs_inst_idx := idx) =
     (merge_callee_state (st with vs_inst_idx := idx) ca with vs_vars := vars)` by
    simp[merge_callee_state_def, venom_state_component_equality] >>
  `ld_joint_control u fn fn'
     (s1 with vs_inst_idx := SUC caller.vs_inst_idx)
     (t1 with vs_inst_idx := SUC caller'.vs_inst_idx)` by
    (qpat_assum `s1 = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `t1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[ld_joint_control_merge_vars]) >>
  qexists_tac `t1` >> simp[] >>
  qpat_x_assum `ld_joint_frame _ _ _ _ _ _ _ _ (DRESTRICT _ _) _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  fs[ld_joint_frame_def, ld_env_agree_def, ld_params_agree_def,
     ld_joint_allocas_def, ld_joint_local_fields_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
