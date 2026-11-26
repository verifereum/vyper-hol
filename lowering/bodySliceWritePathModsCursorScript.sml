(* Cursor transport for the checked straight-line Slice write suffix. *)
Theory bodySliceWritePathModsCursor
Ancestors
  ptrSafeRun ptrDiscipline instMemFrontier memSafeRun contextCodegenRel
  instIdxIndep venomExecSemantics venomExecProps venomState venomInst

Theorem cursor_lookup_not_revert_forward:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME cur /\
  cur.inst_opcode <> RETURNDATACOPY /\ cur.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s
Proof
  strip_tac >> simp[in_revert_forward_def] >> strip_tac >>
  drule_all revert_forward_at_opcode >> simp[]
QED

Theorem ptr_inst_ok_cursor_transport:
  step_inst_base i s = OK t /\ ~is_terminator i.inst_opcode /\
  ~in_revert_forward fn s /\ i.inst_opcode <> RETURNDATACOPY /\
  ptr_inst_ok D lo fuel ctx fn G tn i s ==>
  ptr_inst_ok D lo fuel ctx fn G tn i (s with vs_inst_idx := k)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE` by (drule step_inst_base_OK_not_INVOKE >> simp[]) >>
  `step_inst fuel ctx i s = OK t` by simp[step_inst_non_invoke] >>
  `step_inst fuel ctx i (s with vs_inst_idx := k) =
    OK (t with vs_inst_idx := k)` by
    simp[step_inst_non_invoke,step_inst_inst_idx_indep,exec_result_map_def] >>
  fs[ptr_inst_ok_def,allocas_from_def,allocas_below_fmp_def] >>
  conj_tac
  >- (qpat_x_assum `access_ok lo G fn i s` mp_tac >>
      Cases_on `in_revert_forward fn (s with vs_inst_idx := k)` >>
      simp[access_ok_def] >> strip_tac >> simp[]) >>
  qpat_x_assum `taint_ok fn tn i s` mp_tac >>
  simp[taint_ok_def,about_to_revert_def] >> strip_tac >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >>
  qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED
