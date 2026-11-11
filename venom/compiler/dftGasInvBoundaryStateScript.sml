Theory dftGasInvBoundaryState
Ancestors
  dftGasOracleDefs venomExecSemantics venomState venomInst instIdxIndep
  list option

Definition inv_boundary_eq_def:
  inv_boundary_eq s t <=>
    (s with vs_inst_idx := 0) = (t with vs_inst_idx := 0)
End

Theorem inv_boundary_eq_update:
  inv_boundary_eq s t <=> t = s with vs_inst_idx := t.vs_inst_idx
Proof
  simp[inv_boundary_eq_def] >> eq_tac >> strip_tac
  >- (first_x_assum (mp_tac o Q.AP_TERM `\s:venom_state. s with vs_inst_idx := t.vs_inst_idx`) >> simp[]) >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem inv_boundary_merge:
  inv_boundary_eq s t ==> merge_callee_state caller s = merge_callee_state caller t
Proof
  simp[inv_boundary_eq_update] >> disch_then SUBST1_TAC >> simp[merge_callee_state_def]
QED

Theorem inv_boundary_setup:
  inv_boundary_eq s t ==> setup_callee fn args s = setup_callee fn args t
Proof
  simp[inv_boundary_eq_update] >> disch_then SUBST1_TAC >> simp[setup_callee_def]
QED

Theorem inv_boundary_phis:
  !xs s t u. inv_boundary_eq s t /\ eval_phis s xs = OK u ==>
  ?v. eval_phis t xs = OK v /\
    (u with vs_inst_idx := k) = (v with vs_inst_idx := k)
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  simp[inv_boundary_eq_update] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC
  >- (gvs[] >> simp[]) >>
  `eval_one_phi (s with vs_inst_idx := t.vs_inst_idx) h = eval_one_phi s h` by
    simp[eval_one_phi_def, eval_op_inst_idx] >>
  Cases_on `h.inst_opcode <> PHI` >> gvs[] >>
  gvs[AllCaseEqs()] >>
  first_x_assum (qspecl_then [`s`, `s with vs_inst_idx := t.vs_inst_idx`] mp_tac) >>
  simp[inv_boundary_eq_def] >> strip_tac >>
  simp[] >>
  qpat_x_assum `_ with vs_inst_idx := k = _`
    (mp_tac o Q.AP_TERM `update_var out v`) >> simp[update_var_def]
QED

Theorem inv_boundary_terminator:
  inv_boundary_eq s t /\ is_terminator i.inst_opcode /\
  ev_step orc p d fuel ctx i s = OK u ==>
  ?v. ev_step orc p d fuel ctx i t = OK v /\ inv_boundary_eq u v
Proof
  simp[inv_boundary_eq_update] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def, ev_step_def] >>
  gvs[step_inst_base_opcode_eqs, eval_op_inst_idx, eval_ops_inst_idx,
      jump_to_def, AllCaseEqs()] >>
  qpat_x_assum `_ = OK u` mp_tac >> pairarg_tac >> simp[]
QED

Theorem inv_boundary_current_bb:
  inv_boundary_eq s t ==> s.vs_current_bb = t.vs_current_bb
Proof
  simp[inv_boundary_eq_update] >> disch_then SUBST1_TAC >> simp[]
QED
