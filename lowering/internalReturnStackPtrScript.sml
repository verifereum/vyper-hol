(* Pointer-safe internal return suffixes. *)
Theory internalReturnStackPtr
Ancestors
  stmtSimReturn fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  fragExec venomInst venomState venomExecSemantics
  emitHelper emitHelperProps finite_map list memLocDefs contextCodegenRel codegenRel

Theorem ret_values_frag_ptr:
  !cx ctx PG sa sb id ops rpc vals pc P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id RET (ops ++ [Var rpc]) []] /\
    (!G tn s. P G tn s ==>
      eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc /\
      EVERY (\op. op_taint tn op = {}) (ops ++ [Var rpc]) /\
      stor_taint_ok cx tn s /\
      R (G,tn) (IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  disj2_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id RET (ops ++ [Var rpc]) [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  `step_inst_base (mk_inst id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    (irule step_ret_values >> simp[]) >>
  `step_inst 0 ctx (mk_inst id RET (ops ++ [Var rpc]) []) s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> s` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  qexists_tac `0` >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  simp[run_from_def, Once exec_block_def, ghost_run_def,
       Once ghost_block_def, exit_result_def] >>
  conj_tac >- simp[Once exec_block_def] >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       allocas_from_def, mk_inst_def, EVERY_MEM] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
