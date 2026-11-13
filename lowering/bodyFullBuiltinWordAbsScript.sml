(* Joint finite-horizon simulation of Abs. *)
Theory bodyFullBuiltinWordAbs
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame gasOutcomeFullCompose
  exprSimWordBuiltins exprSimUnopProps fragGasSeqPtr builtinProps
  fragExecMem instMemFrontier memSafeRun instIdxIndep venomExecSemantics
  ptrDiscipline ptrSafeRun finite_map pred_set codegenRel contextCodegenRel venomState
  builtinSimple emitHelper emitHelperProps freshWrites
  exprLoweringProps exprLowering compileEnv venomInst list rich_list

val _ = Parse.hide "body";

Theorem abs_suffix_opcodes:
  !x sa op sb.
    compile_builtin_abs x sa = (op,sb) ==>
    MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
      [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  rpt gen_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem abs_suffix_mem_ok:
  !x sa op sb s.
    compile_builtin_abs x sa = (op,sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule abs_suffix_opcodes >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  `EVERY (\opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL])
     (MAP (\i. i.inst_opcode) (emitted_insts sa sb))` by simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem abs_inst_transition[local]:
  compile_builtin_abs x sa = (op,sb) /\
  MEM i (emitted_insts sa sb) /\
  (!a. MEM a i.inst_operands ==> op_prov G a = NONE /\ op_taint tn a = {}) /\
  step_inst_base i s = OK t /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ t.vs_memory = s.vs_memory /\
  (!D. ptr_inst_ok D lo 0 ctx fn G tn i s) /\
  (!v. MEM v i.inst_outputs ==>
    op_prov (step_prov PG G i t) (Var v) = NONE /\
    op_taint (step_taint i s t tn) (Var v) = {}) /\
  (!a. op_prov G a = NONE /\ op_taint tn a = {} ==>
    op_prov (step_prov PG G i t) a = NONE /\
    op_taint (step_taint i s t tn) a = {}) /\
  (!v. ~MEM v i.inst_outputs ==>
    lookup_var v t = lookup_var v s /\
    FLOOKUP (step_prov PG G i t) v = FLOOKUP G v /\
    op_taint (step_taint i s t tn) (Var v) = op_taint tn (Var v)) /\
  (step_taint i s t tn).t_mem = tn.t_mem /\
  (step_taint i s t tn).t_stor = tn.t_stor /\
  (step_taint i s t tn).t_trans = tn.t_trans /\
  (step_taint i s t tn).t_imm = tn.t_imm
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt gen_tac >> disch_tac >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
  (qpat_assum `step_inst_base _ s = OK t`
    (mp_tac o PURE_REWRITE_RULE [step_inst_base_def]) >>
  pure_rewrite_tac [venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM,
    venomInstTheory.opcode_case_def] >>
  pure_rewrite_tac [exec_pure2_def, exec_pure1_def,
    venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM] >>
  simp_tac (srw_ss()) [AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  rpt (conj_tac >- simp[update_var_def]) >>
  conj_tac >-
   (simp[ptr_inst_ok_def, step_inst_non_invoke, update_var_def,
         access_ok_def, taint_ok_def, source_memory_write_ranges_def,
         source_memory_read_ranges_def] >>
    fs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DEF] >>
    rpt strip_tac >> gvs[] >> metis_tac[]) >>
  pure_rewrite_tac [step_prov_def, out_prov_def, step_taint_def,
    venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM,
    venomInstTheory.opcode_case_def] >>
  simp[set_prov_def, first_prov_def, op_prov_def, set_var_taint_def,
    out_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    update_var_def] >>
  simp[op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    lookup_var_def, mem_taint_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, new_site_bytes_def,
    DRESTRICT_UNIV, FLOOKUP_DEF, FAPPLY_FUPDATE_THM, range_bytes_def] >>
  simp[EXTENSION] >>
  rpt conj_tac >> Cases >> simp[] >> rpt IF_CASES_TAC >> gvs[] >>
  metis_tac[])
QED
