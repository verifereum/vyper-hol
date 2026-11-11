Theory bodyIntCallCompilerUniversal
Ancestors
  bodyIntCallCompilerCallbacks bodyIntCallCompilerAggregate
  bodyIntCallCompilerStaging exprCallBounds exprLowering
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit

Theorem intcall_interval_expr_callback_all:
  (!ce ty e a. expr_size e < bound /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (expr_child_callback bound cfn ce ty e a))
Proof
  rpt strip_tac >> Cases_on `expr_size e < bound` >>
  simp[expr_child_callback_def, intcall_interval_invalid_expr_call]
QED

Theorem intcall_interval_builtin_callback_all:
  (!ce rt ty bi es a. list_size expr_size es < bound /\
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (dispatch ce rt ty bi es a))) ==>
  !ce rt ty bi es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (builtin_child_callback bound dispatch ce rt ty bi es a))
Proof
  rpt strip_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[builtin_child_callback_def, intcall_interval_invalid_expr_call]
QED

Theorem intcall_interval_type_callback_all:
  (!ce vt ty tb rt es a. list_size expr_size es < bound /\
    k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (dispatch ce vt ty tb rt es a))) ==>
  !ce vt ty tb rt es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (type_child_callback bound dispatch ce vt ty tb rt es a))
Proof
  rpt strip_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[type_child_callback_def, intcall_interval_invalid_expr_call]
QED

Theorem intcall_interval_multi_vvs_floor:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_multi_vvs cfn cenv es a))
Proof
  strip_tac >> Induct >> simp[compile_multi_vvs_def, intcall_interval_return] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_return] >> rpt strip_tac >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_return]
QED
