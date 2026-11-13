Theory extRetDispatchResultPtr
Ancestors
  extRetDispatchProtectionPtr exprLoweringProps freshWrites builtinCreate
  builtinSystem emitHelper compileEnv loweringStateRelDefs context venomInst
  pair

Theorem compile_check_create_result_protected:
  compile_check_create_result result rof st = (op,sb) /\
  (!x. result = Var x ==> not_fresh_at st x) /\
  op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, new_block_def, emit_inst_def,
       emit_void_def, emit_op_def, compile_alloc_buffer_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `st` >> simp[]
QED

Theorem emit_op_result_protected[local]:
  emit_op opc ops st = (op,sb) /\ op = Var x ==>
  not_fresh_at sb x
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
       fresh_var_def, emit_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem compile_create_dispatch_result_protected:
  compile_create_dispatch code_ptr len value salt rof st = (op,sb) /\
  op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `salt` >>
  simp[compile_create_dispatch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `!y. result = Var y ==> not_fresh_at cs' y` by
    (rpt strip_tac >> drule_all emit_op_result_protected >> simp[]) >>
  drule_all compile_check_create_result_protected >> simp[]
QED

Theorem compile_raw_call_finish_result_protected:
  compile_raw_call_finish addr data_ptr data_len gas value call_ty
    max_outsize rof out_val out_ptr st = (op,sb) /\
  (!y. out_val = Var y ==> not_fresh_at st y) /\
  op = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  `st.cs_next_var <= sb.cs_next_var` by
    (metis_tac[ci_mono_compile_raw_call_finish, ci_mono_def, pairTheory.SND]) >>
  Cases_on `rof`
  >- (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `0 < max_outsize` >>
      simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `st` >> simp[]) >>
  Cases_on `max_outsize = 0`
  >- (gvs[] >> metis_tac[compile_raw_call_flag_result_protected]) >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, not_fresh_at_def] >>
  decide_tac
QED
