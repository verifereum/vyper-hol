Theory bodyPtrIfExpAssign
Ancestors
  fragGasSeqPtr fragGasPathPtr emitHelper emitHelperProps fragExec
  compileEnv codegenRel contextCodegenRel arithmetic
  ptrSafeRun ptrDiscipline venomInst venomState venomExecSemantics venomExecProofs

Theorem emit_assign_zero_path_ptr:
  emit_inst ASSIGN [src] [out] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand src s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ASSIGN [src] [out])
      (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id ASSIGN [src] [out]) s
      (update_var out w s) tn)
    (OK ((update_var out w s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ASSIGN [src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ASSIGN [src] [out]) s =
     OK (update_var out w s)` by
    simp[mk_inst_def, step_inst_base_def, exec_pure1_def,
         comp_bind_def, comp_return_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id ASSIGN [src] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          allocas_from_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_inst_base_def, exec_pure1_def,
          comp_bind_def, comp_return_def, update_var_def]) >>
  `~is_terminator (mk_inst sa.cs_next_id ASSIGN [src] [out]).inst_opcode /\
   (mk_inst sa.cs_next_id ASSIGN [src] [out]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[mk_inst_def] >> strip_tac >>
  `~((update_var out w s) with
      vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  gvs[ADD1] >> drule (cj 2 gas_path_ptr_rules) >>
  simp[] >> disch_then irule >> simp[gas_path_ptr_rules]
QED
