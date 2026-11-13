(* Counted memory-safe bare internal returns. *)
Theory internalReturnVoidMem
Ancestors
  internalReturnSequenceMem stmtSimReturn stmtSimDefs loweringStateRelDefs
  stmtLowering nonreentrantEquiv emitHelper emitHelperProps exprLoweringProps
  compileEnv context venomState list arithmetic

Theorem compile_internal_void_return_code[local]:
  cenv.ce_return_pc = SOME (PtrVar rpc byte_size) /\
  compile_stmt cenv lctx ty (Return NONE) st = ((),st') ==>
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    return_unlock_insts cenv st.cs_next_id ++
    [mk_inst (st.cs_next_id + LENGTH (return_unlock_insts cenv st.cs_next_id))
       RET [rpc] []]
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def] >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_return_unlock_def, compile_nonreentrant_unlock_def,
      return_unlock_insts_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_internal_void_return_path_mem:
  cenv.ce_return_pc = SOME (PtrVar rpc byte_size) /\
  compile_stmt cenv lctx ty (Return NONE) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand rpc s = SOME pc /\ ~s.vs_call_ctx.cc_static ==>
  ?n. gas_path_mem ctx func s n
    (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (return_unlock_state cenv s))
Proof
  strip_tac >> drule_all compile_internal_void_return_code >> strip_tac >>
  irule (Q.INST [`ops` |-> `[]`] internal_return_values_path_mem) >>
  simp[eval_operands_def] >>
  qexistsl_tac [`pc`, `rpc`, `st`, `st'`] >> metis_tac[ADD_COMM]
QED

Theorem compile_internal_void_return_intret_mem:
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_pc = SOME (PtrVar rpc byte_size) /\
  compile_stmt cenv lctx ty (Return NONE) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand rpc s = SOME pc /\
  stmt_state_rel ctx func cenv cx (es with scopes := []) s ==>
  ?n r. gas_path_mem ctx func s n r /\
    intret_q func cenv cx tv NoneV (es with scopes := []) r
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all compile_internal_void_return_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[intret_q_def] >>
  qexistsl_tac [`s`, `(return_unlock_state cenv s).vs_inst_idx`] >>
  simp[result_rel_def, intret_vals_match_def] >> fs[stmt_state_rel_def]
QED
