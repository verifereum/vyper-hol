(* Allocated bytestring return: pointer-safe execution boundaries. *)
Theory externalReturnBytesPtr
Ancestors
  abiEncoderBytesPtr protectedAllocCorePtr fragExecPtr fragExec loweringHalt
  bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  codegenRel context contextCodegenRel memLocDefs finite_map pred_set words arithmetic

Theorem ptr_inst_ok_return_operand:
  !cx ctx fn G tn s id p len n.
    eval_operand len s = SOME n /\ op_taint tn len = {} /\
    ptr_covers G tn p s (w2n n) /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w+w2n n ==> i NOTIN tn.t_mem) ==>
    !fuel. ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
      (mk_inst id RETURN [Var p;len] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    memory_range_of_operands_def, mk_inst_def, eval_operand_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[mem_read_ops_def] >> metis_tac[]) >>
  conj_tac >-
    (gen_tac >> Cases_on `op = Var p` >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[eval_operand_def, step_taint_def, store_taint_def,
    adopt_reset_def, imm_taint_def, halt_state_def, set_returndata_def, ret_taint_def] >>
  gvs[stor_taint_ok_def, cx_dead_def, SUBSET_DEF] >>
  gen_tac >> Cases_on `x < w2n n` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem ptr_safe_run_return_operand_halt:
  !cx ctx fn PG G tn s bb id p len n.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [Var p;len] []) /\
    eval_operand len s = SOME n /\ op_taint tn len = {} /\
    ptr_covers G tn p s (w2n n) /\ stor_taint_ok cx tn s /\
    ~ctx_has_dalloca ctx /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w+w2n n ==> i NOTIN tn.t_mem) ==>
    !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s /\
      ?ss. run_from fuel ctx fn s = Halt ss
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  conj_tac >-
    (`ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn
       (mk_inst id RETURN [Var p;len] []) s` by
       (irule ptr_inst_ok_return_operand >> metis_tac[]) >>
     simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     gvs[ptr_covers_def, mk_inst_def, eval_operand_def]) >>
  irule_at Any run_from_halt >>
  qrefinel [`_`,`mk_inst id RETURN [Var p;len] []`,`bb`] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  gvs[ptr_covers_def, mk_inst_def, eval_operand_def]
QED
