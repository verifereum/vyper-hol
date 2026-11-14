(* Pointer safety at the last custom-error instruction.  Reverting payload
   bytes need not be clean, but the address and length operands must be. *)
Theory stmtSimCustomErrorPtrBoundary
Ancestors
  fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInstProofs venomInst venomState memLocDefs finite_map contextCodegenRel codegenRel

Theorem custom_error_revert_ptr_inst_ok:
  !D ctx fn G tn s id p len n fuel.
    ptr_covers G tn p s (w2n n) /\
    eval_operand len s = SOME n /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id REVERT [Var p; len] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       about_to_revert_def, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, memory_range_of_operands_def,
       eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
    instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[eval_operand_def, AllCaseEqs()] >> metis_tac[]
QED
