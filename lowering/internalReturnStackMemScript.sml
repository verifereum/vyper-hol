(* Memory safety of internal stack-return suffixes. *)
Theory internalReturnStackMem
Ancestors
  internalReturnVoidMem internalReturnTupleMem internalReturnSequenceMem stmtSimReturn fragGasSeqMem instMemFrontier memSafeRun fragExecMem
  gasCount fragExec runFromGasPathMem loweringStateRelDefs
  valueEncoding stmtSimDefs venomExecSemantics venomInstProofs venomState venomInst
  emitHelperProps exprLoweringProps list rich_list arithmetic

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
  irule (Q.INST [`ops` |-> `[op]`] internal_return_values_path_mem) >>
  simp[eval_operands_def] >>
  qexistsl_tac [`op`, `pc`, `rpc`, `st`, `st'`] >> metis_tac[]
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
