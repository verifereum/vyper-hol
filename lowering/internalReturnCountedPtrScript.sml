(* Counted pointer-safe RET boundary. *)
Theory internalReturnCountedPtr
Ancestors
  stmtSimReturn fragGasPathPtr ptrSafeRun ptrDiscipline gasCount
  fragExec emitHelper emitHelperProps venomInst venomState venomExecSemantics
  contextCodegenRel codegenRel list rich_list

Theorem emit_ret_values_path_ptr:
  emit_inst RET (ops ++ [Var rpc]) [] sa = ((),sb) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc /\
  EVERY (\op. op_taint tn op = {}) (ops ++ [Var rpc]) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_path_ptr D lo ctx func PG G tn s 0 G tn
    (IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    (irule step_ret_values >> simp[]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       exit_result_def, ptr_safe_step_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       mk_inst_def, EVERY_MEM] >>
  fs[mk_inst_def, EVERY_MEM] >> metis_tac[]
QED
