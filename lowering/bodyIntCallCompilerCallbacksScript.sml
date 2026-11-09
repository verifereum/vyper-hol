Theory bodyIntCallCompilerCallbacks
Ancestors
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit exprCallBounds exprSimHypsDefs

Theorem intcall_interval_invalid_expr_call:
  intcall_compiler_interval k a (SND (invalid_expr_call ty a))
Proof
  simp[invalid_expr_call_def, pairTheory.UNCURRY] >>
  irule intcall_interval_emit_inst >> simp[]
QED

Theorem intcall_interval_expr_child_callback:
  (!ce ty e a. expr_size e < bound /\ ~expr_has_effect e /\
      k <= a.cs_next_var ==>
      intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce ty e a. ~expr_has_effect e /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (expr_child_callback bound cfn ce ty e a))
Proof
  rpt strip_tac >> Cases_on `expr_size e < bound` >>
  simp[expr_child_callback_def, intcall_interval_invalid_expr_call]
QED

Theorem intcall_interval_builtin_child_callback:
  (!ce rt ty bi es a. list_size expr_size es < bound /\
      EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
      intcall_compiler_interval k a (SND (dispatch ce rt ty bi es a))) ==>
  !ce rt ty bi es a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (builtin_child_callback bound dispatch ce rt ty bi es a))
Proof
  rpt strip_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[builtin_child_callback_def, intcall_interval_invalid_expr_call]
QED

Theorem intcall_interval_type_child_callback:
  (!ce vt ty tb rt es a. list_size expr_size es < bound /\
      EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
      intcall_compiler_interval k a (SND (dispatch ce vt ty tb rt es a))) ==>
  !ce vt ty tb rt es a. EVERY (\e. ~expr_has_effect e) es /\ k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (type_child_callback bound dispatch ce vt ty tb rt es a))
Proof
  rpt strip_tac >> Cases_on `list_size expr_size es < bound` >>
  simp[type_child_callback_def, intcall_interval_invalid_expr_call]
QED
