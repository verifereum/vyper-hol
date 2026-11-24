Theory namedConstDispatchResult
Ancestors
  exprLowering context compileEnv

Theorem named_const_dispatch_not_label:
  compile_builtin_dispatch_body f ce vt ty NamedConst args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rename1 `lower_value _ _ _ _ _ = (opnd,_)` >>
  Cases_on `is_word_type vt` >> Cases_on `opnd` >>
  gvs[as_stack_val_def, as_ptr_val_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def]
QED
