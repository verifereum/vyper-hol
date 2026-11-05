Theory extRetDispatchProtectionPtr
Ancestors
  builtinCreate builtinSystem emitHelper compileEnv context venomInst pair

Theorem compile_create_dispatch_unchecked_result_protected:
  compile_create_dispatch code_ptr len value salt F st = (op,sb) /\
  op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `salt` >>
  simp[compile_create_dispatch_def, compile_check_create_result_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem compile_raw_call_flag_result_protected:
  compile_raw_call_finish addr data_ptr data_len gas value
    call_ty 0 F out_val out_ptr st = (op,sb) /\
  op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `call_ty` >>
  simp[compile_raw_call_finish_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED
