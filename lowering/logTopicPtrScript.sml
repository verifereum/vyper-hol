(* Pointer checks for indexed log topic hashing. *)
Theory logTopicPtr
Ancestors
  logInstSeqPtr logValueFramePtr bodyPtrDefs codegenRel ptrCoverage ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  contextCodegenRelProps contextCodegenRel memLocDefs finite_map words

Theorem ptr_inst_ok_sha3_clean:
  ptr_covers G tn src s (w2n n) /\
  lookup_var src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id SHA3 [Var src;len] [out]) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, eval_operand_def] >>
  simp[memory_range_of_operands_def, eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def, update_var_def] >> rpt strip_tac >> gvs[]
QED
