(* Memory safety of internal stack-return suffixes. *)
Theory internalReturnStackMem
Ancestors
  stmtSimReturn fragGasSeqMem instMemFrontier memSafeRun fragExecMem
  gasCount fragExec runFromGasPathMem loweringStateRelDefs
  valueEncoding stmtSimDefs venomExecSemantics venomInstProofs venomState venomInst
  emitHelperProps exprLoweringProps list rich_list arithmetic

Theorem internal_word_return_mem_safe:
  !cenv st st' func ctx s op rpc w pc fuel.
  fn_has_code st st' func /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [op;rpc] []] /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME w /\ eval_operand rpc s = SOME pc /\
  ~s.vs_call_ctx.cc_static ==>
  mem_safe_run fuel ctx func s
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `st'.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. _` (fn th =>
    assume_tac (Q.SPEC `0` th) >> assume_tac (Q.SPEC `1` th)) >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def] >>
  simp[mem_safe_run_def, Once mem_safe_block_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def] >>
  simp[Once exec_block_def, is_terminator_def] >>
  simp[step_inst_non_invoke] >>
  simp[mk_inst_def] >>
  simp[SRULE [mk_inst_def] step_internal_word_return,
       SRULE [mk_inst_def] step_persistent_return_unlock,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit] >>
  simp[eval_operand_def] >>
  simp[Once mem_safe_block_def, Once exec_block_def, ADD1,
       step_inst_non_invoke, mk_inst_def, mem_safe_step_non_invoke,
       below_frontier_no_ranges, inst_dload_in_section_other,
       SRULE [mk_inst_def] step_internal_word_return,
       is_terminator_def]
QED

Theorem compile_internal_word_return_path_mem:
  is_word_type ty /\ cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME w /\ eval_operand rpc s = SOME pc /\
  ~s.vs_call_ctx.cc_static ==>
  ?n. gas_path_mem ctx func s n
    (IntRet <| iret_values := [w]; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s))
Proof
  strip_tac >> drule_all compile_internal_word_return_code >> strip_tac >>
  irule run_from_gas_path_mem >> simp[exit_result_def] >>
  qexists_tac `0` >> conj_tac
  >- (irule internal_word_return_run >> metis_tac[]) >>
  irule internal_word_return_mem_safe >> metis_tac[]
QED

Theorem compile_internal_word_return_intret_mem:
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  compile_internal_return_from_env cenv ty src_ty op rpc st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  expr_val_rel cx ty v op s /\ eval_operand rpc s = SOME pc /\
  stmt_state_rel ctx func cenv cx (es with scopes := []) s ==>
  ?n r. gas_path_mem ctx func s n r /\
    intret_q func cenv cx tv v (es with scopes := []) r
Proof
  strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    gvs[loweringPostsTheory.expr_val_rel_def] >>
  `~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all compile_internal_word_return_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[intret_q_def] >>
  qexists_tac `s` >>
  simp[result_rel_def] >> conj_tac
  >- fs[stmt_state_rel_def] >>
  metis_tac[intret_vals_match_word]
QED
