Theory bodyIntCallCompilerUnwrap
Ancestors
  bodyIntCallCompilerContext bodyIntCallCompilerEmit exprLowering context

Theorem intcall_interval_unwrap_value:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (unwrap_value cenv vv a))
Proof
  Cases_on `vv` >> simp[unwrap_value_def, intcall_interval_return] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty`
  >- simp[intcall_interval_ptr_load] >>
  Cases_on `p.ptr_location` >>
  simp[intcall_interval_return, intcall_interval_ensure_in_memory]
QED
