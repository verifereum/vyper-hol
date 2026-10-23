Theory immutableCopyExecution
Ancestors
  immutableWordExecution immutableMemoryFrame emitHelperProps
  context compileEnv emitHelper exprLoweringProps venomState venomExecSemantics venomInst

(* The offset helper either folds a literal or emits a single ADD.  Its
   semantic frame is the interface needed to keep the copy's root operands
   stable while allocating address temporaries. *)
Theorem immutable_byte_offset_execution:
  compile_lit_byte_offset op off st = (result,st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand result s' = SOME (a + n2w off) /\
    fresh_vars_wrt st' s' /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p s' = SOME w) /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, wordsTheory.WORD_ADD_0]) >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `s` >>
      gvs[emitted_insts_def, run_inst_seq_def, eval_operand_def]) >>
  qexists_tac `update_var ("%" ++ toString st.cs_next_var) (a + n2w off) s` >>
  simp[emitted_insts_def, run_inst_seq_def, listTheory.DROP_APPEND,
       mk_inst_def, step_inst_base_def, exec_pure2_def,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  (conj_tac >- gvs[fresh_vars_wrt_def]) >>
  rpt strip_tac >> Cases_on `p` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[fresh_vars_wrt_def, finite_mapTheory.FLOOKUP_DEF]
QED
