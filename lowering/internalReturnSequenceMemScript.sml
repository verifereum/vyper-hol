(* Shared optional-unlock and stack-value RET epilogue. *)
Theory internalReturnSequenceMem
Ancestors
  stmtSimReturn internalReturnLockProps fragGasSeqMem instMemFrontier
  memSafeRun fragExecMem gasCount fragExec runFromGasPathMem
  venomExecSemantics venomInstProofs venomState venomInst
  emitHelperProps exprLoweringProps list rich_list arithmetic

Theorem internal_return_values_run_mem:
  !cenv st st' func ctx s ops rpc vals pc fuel.
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET (ops ++ [rpc]) []] /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operands ops s = SOME vals /\ eval_operand rpc s = SOME pc /\
  ~s.vs_call_ctx.cc_static ==>
  run_from 0 ctx func s =
    IntRet <| iret_values := vals; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s) /\
  mem_safe_run fuel ctx func s
Proof
  rpt gen_tac >> strip_tac >>
  `!ss id. eval_operands ops ss = SOME vals /\ eval_operand rpc ss = SOME pc ==>
     step_inst_base (mk_inst id RET (ops ++ [rpc]) []) ss =
     IntRet <| iret_values := vals; iret_adopt_fmp := NONE |> ss` by
    metis_tac[internalReturnLockPropsTheory.step_RET_values] >>
  pop_assum (assume_tac o PURE_REWRITE_RULE [mk_inst_def]) >>
  `!key value. eval_operands ops (sstore key value s) = SOME vals` by
    (rpt gen_tac >>
     `eval_operands ops (sstore key value s) = eval_operands ops s` suffices_by simp[] >>
     irule eval_operands_agree >> simp[eval_operand_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    assume_tac (Q.SPEC `0` th) >> assume_tac (Q.SPEC `1` th)) >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  simp[run_from_def, mem_safe_run_def, Once mem_safe_block_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def] >>
  simp[Once exec_block_def, is_terminator_def] >>
  simp[step_inst_non_invoke, mk_inst_def] >>
  simp[SRULE [mk_inst_def] step_persistent_return_unlock,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit] >>
  simp[eval_operand_def] >>
  simp[Once mem_safe_block_def, Once exec_block_def, ADD1,
       step_inst_non_invoke, mk_inst_def, mem_safe_step_non_invoke,
       below_frontier_no_ranges, inst_dload_in_section_other,
       is_terminator_def] >>
  simp[Once run_block_non_phis_def, step_inst_non_invoke, mk_inst_def,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit,
       SRULE [mk_inst_def] step_persistent_return_unlock, is_terminator_def] >>
  simp[Once run_block_non_phis_def, step_inst_non_invoke, mk_inst_def,
       ADD1, eval_operand_def]
QED

Theorem internal_return_values_path_mem:
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET (ops ++ [rpc]) []] /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operands ops s = SOME vals /\ eval_operand rpc s = SOME pc /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted ==>
  ?n. gas_path_mem ctx func s n
    (IntRet <| iret_values := vals; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s))
Proof
  strip_tac >> irule run_from_gas_path_mem >> simp[exit_result_def] >>
  qexists_tac `0` >> irule internal_return_values_run_mem >> metis_tac[]
QED
