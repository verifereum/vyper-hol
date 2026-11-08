(* Interface probes for augmented assignment.  Scalar robustness and clean
   MLOAD are already exported by representationCleanPtr and typedCopyPtr;
   do not duplicate them here. *)
Theory augAssignPtrInterfaces
Ancestors
  typedCopyPtr representationCleanPtr fragGasSeqPtr stmtAbortPtr
  ptrSafeRun ptrDiscipline venomInst venomState venomExecSemantics
  codegenRel contextCodegenRel

Theorem clean_add_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [tmp]) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  step_inst_base (mk_inst id ADD [left;right] [tmp]) s = OK u /\
  gas_path_ptr D 0 ctx fn PG
    (step_prov PG G (mk_inst id ADD [left;right] [tmp]) u)
    (step_taint (mk_inst id ADD [left;right] [tmp]) s u tn)
    (u with vs_inst_idx := SUC s.vs_inst_idx) n G' tn' r ==>
  gas_path_ptr D 0 ctx fn PG G tn s n G' tn' r
Proof
  strip_tac >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
  simp[mk_inst_def, is_terminator_def] >>
  impl_tac >- (irule (SIMP_RULE (srw_ss()) [mk_inst_def] ptr_inst_ok_copy_len_binop) >> simp[]) >>
  simp[]
QED

Theorem ptr_inst_ok_assert:
  op_taint tn cond = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [cond] []) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem assert_abort_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [cond] []) /\
  op_taint tn cond = {} /\
  step_inst_base (mk_inst id ASSERT [cond] []) s = Abort a t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [cond] []) s` by
    (irule ptr_inst_ok_assert >> simp[]) >>
  mp_tac (Q.INST [`lo` |-> `0`, `i` |-> `mk_inst id ASSERT [cond] []`] gas_path_ptr_abort) >>
  gvs[mk_inst_def, is_terminator_def]
QED
