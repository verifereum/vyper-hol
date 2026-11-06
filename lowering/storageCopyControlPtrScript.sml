(* Counted control edges for checked storage-copy loops. *)
Theory storageCopyControlPtr
Ancestors
  fragGasPathPtr ptrSafeRun ptrDiscipline gasCount venomInst venomState
  venomExecSemantics venomExecProofs codegenRel contextCodegenRel

Theorem storage_copy_jump_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem storage_copy_branch_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label lt; Label lf] []) /\
  eval_operand op s = SOME (if test then 1w else 0w) /\
  op_taint tn op = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (jump_to (if test then lt else lf) s))
Proof
  strip_tac >> drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `id`] assume_tac) >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `test` >> gvs[op_taint_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label lt` >> gvs[] >>
     Cases_on `op' = Label lf` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn
     (OK (jump_to (if test then lt else lf) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jnz_behavior, is_terminator_def] >>
     Cases_on `test` >> gvs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (if test then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED
