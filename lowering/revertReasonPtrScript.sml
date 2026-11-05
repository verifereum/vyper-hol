(* Instruction boundaries for the shared revert encoder. *)
Theory revertReasonPtr
Ancestors
  reasonRepresentationPtr fragExecPtr fragGasSeqPtr stmtAbortPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline venomInst venomState
  venomExecSemantics words codegenRel contextCodegenRel memLocDefs

Theorem ptr_inst_ok_revert:
  ptr_covers G tn p s (w2n n) /\
  eval_operand len s = SOME n /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx ==>
  !fuel. ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id REVERT [Var p; len] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def,
       about_to_revert_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, eval_operand_def]
QED
