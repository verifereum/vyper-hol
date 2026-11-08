Theory bodyPtrBytestringBuiltinsCompilerAllocationTrace
Ancestors bodyPtrBytestringBuiltinsOpenBodyAllocationTrace
          bodyPtrBytestringBuiltinsGuardedAllocationTrace exprLowering

Theorem compiler_allocation_trace:
  (!ce ty e s. allocation_trace s (SND (compile_expr ce ty e s))) /\
  (!ce rt ty bi es s. allocation_trace s
    (SND (compile_builtin_dispatch ce rt ty bi es s))) /\
  (!ce vt ty tb rt es s. allocation_trace s
    (SND (compile_type_builtin_dispatch ce vt ty tb rt es s)))
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_expr_raw_def] >>
  simp[compile_expr_body_allocation_trace,
       compile_builtin_dispatch_body_allocation_trace,
       compile_type_builtin_dispatch_body_allocation_trace,
       expr_child_callback_allocation_trace,
       builtin_child_callback_allocation_trace,
       type_child_callback_allocation_trace]
QED

Theorem compile_expr_allocation_trace[simp]:
  !ce ty e s. allocation_trace s (SND (compile_expr ce ty e s))
Proof
  simp[compiler_allocation_trace]
QED

Theorem compile_builtin_dispatch_allocation_trace[simp]:
  !ce rt ty bi es s. allocation_trace s
    (SND (compile_builtin_dispatch ce rt ty bi es s))
Proof
  simp[compiler_allocation_trace]
QED

Theorem compile_type_builtin_dispatch_allocation_trace[simp]:
  !ce vt ty tb rt es s. allocation_trace s
    (SND (compile_type_builtin_dispatch ce vt ty tb rt es s))
Proof
  simp[compiler_allocation_trace]
QED
