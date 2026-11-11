Theory bodyIntCallCompilerClosure
Ancestors
  bodyIntCallCompilerExprBody bodyIntCallCompilerBuiltin
  bodyIntCallCompilerTypeBuiltin bodyIntCallCompilerUniversal
  bodyIntCallCompilerInterval exprLowering

Theorem intcall_interval_compile_size[local]:
  !n.
    (!ce ty e a k. expr_size e = n /\ k <= a.cs_next_var ==>
      intcall_compiler_interval k a (SND (compile_expr ce ty e a))) /\
    (!ce rt ty bi es a k. list_size expr_size es = n /\ k <= a.cs_next_var ==>
      intcall_compiler_interval k a
        (SND (compile_builtin_dispatch ce rt ty bi es a))) /\
    (!ce vt ty tb rt es a k. list_size expr_size es = n /\ k <= a.cs_next_var ==>
      intcall_compiler_interval k a
        (SND (compile_type_builtin_dispatch ce vt ty tb rt es a)))
Proof
  completeInduct_on `n` >> conj_tac
  >- (rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
      irule intcall_interval_expr_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >> rpt conj_tac
      >- simp[intcall_interval_expr_callback_all]
      >- simp[intcall_interval_builtin_callback_all] >>
      simp[intcall_interval_type_callback_all]) >>
  conj_tac
  >- (rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
      irule intcall_interval_builtin_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
      simp[intcall_interval_expr_callback_all]) >>
  rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
  irule intcall_interval_type_builtin_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
  simp[intcall_interval_expr_callback_all]
QED

Theorem intcall_interval_compile_expr:
  !ce ty e a k. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (compile_expr ce ty e a))
Proof
  metis_tac[intcall_interval_compile_size]
QED

Theorem intcall_interval_compile_builtin_dispatch:
  !ce rt ty bi es a k. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_builtin_dispatch ce rt ty bi es a))
Proof
  metis_tac[intcall_interval_compile_size]
QED

Theorem intcall_interval_compile_type_builtin_dispatch:
  !ce vt ty tb rt es a k. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_type_builtin_dispatch ce vt ty tb rt es a))
Proof
  metis_tac[intcall_interval_compile_size]
QED

Theorem intcall_interval_compile_multi_vvs:
  !ce es a k. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_multi_vvs compile_expr ce es a))
Proof
  simp[intcall_interval_multi_vvs_floor, intcall_interval_compile_expr]
QED
