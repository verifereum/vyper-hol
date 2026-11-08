Theory bodyPtrBytestringBuiltinsGuardedAllocationTrace
Ancestors bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace exprCallBounds emitHelper compileEnv

Theorem invalid_expr_call_allocation_trace[simp]:
  !ty s. allocation_trace s (SND (invalid_expr_call ty s))
Proof
  rpt gen_tac >> simp[invalid_expr_call_def] >> pairarg_tac >> gvs[] >>
  metis_tac[allocation_trace_emit_inst]
QED

Theorem expr_child_callback_allocation_trace:
  !bound cfn.
  (!cenv ty e s. expr_size e < bound ==>
    allocation_trace s (SND (cfn cenv ty e s))) ==>
  !cenv ty e s.
    allocation_trace s (SND (expr_child_callback bound cfn cenv ty e s))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >> IF_CASES_TAC >> simp[]
QED

Theorem builtin_child_callback_allocation_trace:
  !bound bfn.
  (!cenv rt ty bi args s. list_size expr_size args < bound ==>
    allocation_trace s (SND (bfn cenv rt ty bi args s))) ==>
  !cenv rt ty bi args s.
    allocation_trace s (SND (builtin_child_callback bound bfn cenv rt ty bi args s))
Proof
  rpt strip_tac >> simp[builtin_child_callback_def] >> IF_CASES_TAC >> simp[]
QED

Theorem type_child_callback_allocation_trace:
  !bound tfn.
  (!cenv vt ty tb rt args s. list_size expr_size args < bound ==>
    allocation_trace s (SND (tfn cenv vt ty tb rt args s))) ==>
  !cenv vt ty tb rt args s.
    allocation_trace s (SND (type_child_callback bound tfn cenv vt ty tb rt args s))
Proof
  rpt strip_tac >> simp[type_child_callback_def] >> IF_CASES_TAC >> simp[]
QED
