(* The operational and pointer checks for the return-data size opcode. *)
Theory returndataSizePtr
Ancestors
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel words list

Theorem raw_call_returndatasize_step_base:
  step_inst_base (mk_inst iid RETURNDATASIZE [] [out]) s =
    OK (update_var out (n2w (LENGTH s.vs_returndata)) s)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
    venomExecSemanticsTheory.bind_outputs_def]
QED

Theorem ptr_inst_ok_returndatasize:
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx func G tn (mk_inst iid RETURNDATASIZE [] [out]) s
Proof
  strip_tac >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
    ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomInstTheory.mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_read0_def,
    venomExecSemanticsTheory.bind_outputs_def, venomStateTheory.update_var_def] >>
  rpt strip_tac >> gvs[]
QED
