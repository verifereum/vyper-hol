Theory bodyPtrStructLitOwnershipCallbacks
Ancestors bodyPtrStructLitOwnershipSteps exprCallBounds vyperAST

Theorem alloc_run_expr_child_callback_fallback:
  (expr_size e < n ==> alloc_run P (cfn ce ty e) Q) /\
  alloc_run P (invalid_expr_call (expr_type e)) Q ==>
  alloc_run P (expr_child_callback n cfn ce ty e) Q
Proof
  Cases_on `expr_size e < n` >>
  simp[alloc_run_def, expr_child_callback_def] >> metis_tac[]
QED

Theorem alloc_run_builtin_child_callback_fallback:
  (list_size expr_size es < n ==> alloc_run P (bfn ce rt ty bi es) Q) /\
  alloc_run P (invalid_expr_call rt) Q ==>
  alloc_run P (builtin_child_callback n bfn ce rt ty bi es) Q
Proof
  Cases_on `list_size expr_size es < n` >>
  simp[alloc_run_def, builtin_child_callback_def] >> metis_tac[]
QED

Theorem alloc_run_type_child_callback_fallback:
  (list_size expr_size es < n ==> alloc_run P (tfn ce vt ty tb rt es) Q) /\
  alloc_run P (invalid_expr_call vt) Q ==>
  alloc_run P (type_child_callback n tfn ce vt ty tb rt es) Q
Proof
  Cases_on `list_size expr_size es < n` >>
  simp[alloc_run_def, type_child_callback_def] >> metis_tac[]
QED

Theorem alloc_run_invalid_expr_call_conseq:
  (!st. Q (StackValue ty (Lit 0w)) st) ==>
  alloc_run P (invalid_expr_call ty) Q
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_invalid_expr_call >> simp[]
QED

Theorem alloc_run_expr_child_callback:
  (expr_size e < n ==> alloc_run P (cfn ce ty e) Q) /\
  (!st. Q (StackValue (expr_type e) (Lit 0w)) st) ==>
  alloc_run P (expr_child_callback n cfn ce ty e) Q
Proof
  strip_tac >> irule alloc_run_expr_child_callback_fallback >>
  simp[alloc_run_invalid_expr_call_conseq]
QED

Theorem alloc_run_builtin_child_callback:
  (list_size expr_size es < n ==> alloc_run P (bfn ce rt ty bi es) Q) /\
  (!st. Q (StackValue rt (Lit 0w)) st) ==>
  alloc_run P (builtin_child_callback n bfn ce rt ty bi es) Q
Proof
  strip_tac >> irule alloc_run_builtin_child_callback_fallback >>
  simp[alloc_run_invalid_expr_call_conseq]
QED

Theorem alloc_run_type_child_callback:
  (list_size expr_size es < n ==> alloc_run P (tfn ce vt ty tb rt es) Q) /\
  (!st. Q (StackValue vt (Lit 0w)) st) ==>
  alloc_run P (type_child_callback n tfn ce vt ty tb rt es) Q
Proof
  strip_tac >> irule alloc_run_type_child_callback_fallback >>
  simp[alloc_run_invalid_expr_call_conseq]
QED

Theorem alloc_run_expr_child_callback_owned:
  (expr_size e < n ==> alloc_run P (cfn ce ty e) (\v st. T)) ==>
  alloc_run P (expr_child_callback n cfn ce ty e) (\v st. T)
Proof simp[alloc_run_expr_child_callback]
QED

Theorem alloc_run_builtin_child_callback_owned:
  (list_size expr_size es < n ==>
    alloc_run P (bfn ce rt ty bi es) (\v st. T)) ==>
  alloc_run P (builtin_child_callback n bfn ce rt ty bi es) (\v st. T)
Proof simp[alloc_run_builtin_child_callback]
QED

Theorem alloc_run_type_child_callback_owned:
  (list_size expr_size es < n ==>
    alloc_run P (tfn ce vt ty tb rt es) (\v st. T)) ==>
  alloc_run P (type_child_callback n tfn ce vt ty tb rt es) (\v st. T)
Proof simp[alloc_run_type_child_callback]
QED
