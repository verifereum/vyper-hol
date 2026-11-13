(* Counted execution of the implicit guard release and bare RET. *)
Theory bodyIntCallNrEpiloguePath
Ancestors
  bodyIntCallSharpReturn stmtSimReturn transientLockProps
  emitHelperProps emitHelper compileEnv fragExec fragGasPath gasCount
  venomExecSemantics venomInst venomState

Theorem intcall_unlock_ret_path:
  !ce sb su rpc sf func u ctx.
  compile_return_unlock ce sb = ((),su) /\
  emit_inst RET [rpc] [] su = ((),sf) /\ fn_has_code sb sf func /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~u.vs_call_ctx.cc_static /\ (?pc. eval_operand rpc u = SOME pc) ==>
  gas_path ctx func u 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state ce u))
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_return_unlock_shape >> strip_tac >>
  `sf.cs_current_bb = su.cs_current_bb /\
   sf.cs_current_insts = su.cs_current_insts ++
     [mk_inst su.cs_next_id RET [rpc] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  `sf.cs_current_bb = sb.cs_current_bb /\
   sf.cs_current_insts = sb.cs_current_insts ++
     (return_unlock_insts ce sb.cs_next_id ++ [mk_inst su.cs_next_id RET [rpc] []])` by
    simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0 /\ ~info3`
  >- (qpat_x_assum `!i. _` (fn th =>
        assume_tac (Q.SPEC `0` th) >> assume_tac (Q.SPEC `1` th)) >>
      gvs[return_unlock_insts_def, return_unlock_state_def] >>
      qmatch_goalsub_abbrev_tac `IntRet _ v` >>
      `gas_path_edge ctx func u 0 (OK v)` by
        (simp[gas_path_edge_def] >>
         qexists `0` >>
         Cases_on `info2` >>
         simp[mk_inst_def, gas_count_step_def, step_inst_non_invoke] >>
         disj1_tac >>
         simp[step_inst_base_opcode_eqs] >>
         simp[exec_write2_def, eval_operands_def, eval_operand_def] >>
         simp[tstore_def, sstore_def, Abbr `v`, exit_result_def,
              is_terminator_def]) >>
      `gas_path ctx func v 0
         (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> v)` by
        (irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
         Cases_on `info2` >>
         simp[gas_path_edge_def, Abbr `v`, tstore_def, sstore_def,
              arithmeticTheory.ADD1] >>
         qexists `0` >>
         simp[gas_count_step_def, step_inst_non_invoke, mk_inst_def] >>
         disj2_tac >>
         simp[step_inst_base_opcode_eqs] >> simp[] >>
         Cases_on `rpc` >>
         gvs[eval_operands_def, eval_operand_def, lookup_var_def,
             tstore_def, sstore_def, exit_result_def]) >>
      metis_tac[cj 2 gas_path_rules, arithmeticTheory.ADD]) >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >> qexists `0` >>
  simp[gas_count_step_def, step_inst_non_invoke, mk_inst_def] >>
  disj2_tac >> simp[step_inst_base_opcode_eqs] >> simp[] >>
  simp[eval_operands_def, exit_result_def]
QED
