(* Runtime data-section loads for reason normalization. *)
Theory reasonCodePtr
Ancestors
  reasonPrefixPtr fragExecPtr ptrSafeRun ptrDiscipline venomInst venomState
  venomExecSemantics compileEnv codegenRel memLocDefs contextCodegenRel

Theorem ptr_inst_ok_dload:
  op_taint tn src = {} /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id DLOAD [src] [dst]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_output_clean:
  out_taint tn (mk_inst id DLOAD [src] [dst]) s = {} /\
  out_prov PG G (mk_inst id DLOAD [src] [dst]) u = NONE
Proof
  simp[out_taint_def, out_prov_def, mk_inst_def] >>
  Cases_on `eval_operand src s` >> simp[]
QED

Theorem reason_code_dload_path_ptr:
  emit_inst DLOAD [src] [dst] sa = ((),sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst sa.cs_next_id DLOAD [src] [dst]) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id DLOAD [src] [dst]) t)
    (step_taint (mk_inst sa.cs_next_id DLOAD [src] [dst]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[ptr_inst_ok_dload, is_terminator_def] >>
  qexists_tac `sb` >> simp[]
QED
