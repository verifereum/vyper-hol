Theory bodyPtrBopInOperandBoundary
Ancestors bodyPtrMakeArray bodyPtrPreds

(* make_array_expr_ptr_ok is an inherited locally admitted ancestor, permitted
   by TASK_bopin.  This reduction does not assume the target membership lemma. *)
Theorem singleton_array_operands_ptr:
  body_expr_ptr_ok cx x /\ body_expr_ptr_ok cx y ==>
  body_exprs_ptr_ok cx
    [x; Builtin (ArrayT t (Fixed 1)) (MakeArray (SOME t) (Fixed 1)) [y]]
Proof
  strip_tac >> simp[body_exprs_ptr_ok_def] >> strip_tac >>
  irule make_array_expr_ptr_ok >> simp[body_exprs_ptr_ok_def]
QED
