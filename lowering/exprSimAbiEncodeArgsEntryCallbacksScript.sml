Theory exprSimAbiEncodeArgsEntryCallbacks
Ancestors
  exprSimAbiEncodeArgsEntryValue exprSimAbiEncodeArgsEntryPrim
  exprCallBounds compileEnv context emitHelper

Theorem abi_args_entry_invalid_call:
  invalid_expr_call ty a = (vv,b) ==> cs_extends a b /\
    (a.cs_current_insts = [] ==> abi_args_entry_emitted a b)
Proof
  simp[invalid_expr_call_def] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> `INVALID <> PHI` by simp[] >>
  metis_tac[fragExecTheory.cs_extends_emit_inst, abi_args_entry_emit_inst]
QED

Theorem abi_args_entry_expr_callback_safe:
  (!ce ty e a vv b. expr_size e < n /\ f ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce ty e a vv b. expr_child_callback n f ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  rpt strip_tac >> gvs[expr_child_callback_def] >>
  Cases_on `expr_size e < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_builtin_callback_safe:
  (!ce rt ty bi args a vv b. list_size expr_size args < n /\
     f ce rt ty bi args a = (vv,b) ==>
     cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce rt ty bi args a vv b.
    builtin_child_callback n f ce rt ty bi args a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  rpt strip_tac >> gvs[builtin_child_callback_def] >>
  Cases_on `list_size expr_size args < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_type_callback_safe:
  (!ce vt ty tb rt args a vv b. list_size expr_size args < n /\
     f ce vt ty tb rt args a = (vv,b) ==>
     cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce vt ty tb rt args a vv b.
    type_child_callback n f ce vt ty tb rt args a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  rpt strip_tac >> gvs[type_child_callback_def] >>
  Cases_on `list_size expr_size args < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call, abi_args_entry_safe_def]
QED

Theorem abi_args_entry_expr_callback_emitted:
  (!ce ty e a vv b. expr_size e < n /\ P ce ty e /\
     f ce ty e a = (vv,b) /\ a.cs_current_insts = [] ==>
     abi_args_entry_emitted a b) ==>
  !ce ty e a vv b. P ce ty e /\
    expr_child_callback n f ce ty e a = (vv,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b
Proof
  rpt strip_tac >> gvs[expr_child_callback_def] >>
  Cases_on `expr_size e < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call]
QED

Theorem abi_args_entry_builtin_callback_emitted:
  (!ce rt ty bi args a vv b. list_size expr_size args < n /\
     P ce rt ty bi args /\ f ce rt ty bi args a = (vv,b) /\
     a.cs_current_insts = [] ==> abi_args_entry_emitted a b) ==>
  !ce rt ty bi args a vv b. P ce rt ty bi args /\
    builtin_child_callback n f ce rt ty bi args a = (vv,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b
Proof
  rpt strip_tac >> gvs[builtin_child_callback_def] >>
  Cases_on `list_size expr_size args < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call]
QED

Theorem abi_args_entry_type_callback_emitted:
  (!ce vt ty tb rt args a vv b. list_size expr_size args < n /\
     P ce vt ty tb rt args /\ f ce vt ty tb rt args a = (vv,b) /\
     a.cs_current_insts = [] ==> abi_args_entry_emitted a b) ==>
  !ce vt ty tb rt args a vv b. P ce vt ty tb rt args /\
    type_child_callback n f ce vt ty tb rt args a = (vv,b) /\
    a.cs_current_insts = [] ==> abi_args_entry_emitted a b
Proof
  rpt strip_tac >> gvs[type_child_callback_def] >>
  Cases_on `list_size expr_size args < n` >> gvs[] >>
  metis_tac[abi_args_entry_invalid_call]
QED

Theorem abi_args_entry_guarded_lower_value:
  (!ce ty e a vv b. expr_size e < n /\ f ce ty e a = (vv,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b) ==>
  !ce ty e a x b. lower_value (expr_child_callback n f) ce ty e a = (x,b) ==>
    cs_extends a b /\ abi_args_entry_safe a b
Proof
  strip_tac >> drule abi_args_entry_expr_callback_safe >> strip_tac >>
  metis_tac[abi_args_entry_lower_value]
QED
