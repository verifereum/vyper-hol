(* A raw JMP edge does not execute PHIs in its destination block. *)
Theory exprPtrUnwrapBackedge
Ancestors
  fragGasPathPtr gasCount ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  codegenRel contextCodegenRel

Theorem copy_jmp_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label target] []) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn
    (OK (jump_to target s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JMP [Label target] []) s =
    OK (jump_to target s)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def] >>
  `ptr_safe_step D lo 0 ctx fn PG G tn
    (mk_inst id JMP [Label target] []) s` by
    simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
         source_memory_write_ranges_def, source_memory_read_ranges_def,
         mk_inst_def, op_taint_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[gas_count_step_def, mk_inst_def, is_terminator_def] >>
  disj2_tac >> disj1_tac >> qexists_tac `target` >> simp[]
QED
