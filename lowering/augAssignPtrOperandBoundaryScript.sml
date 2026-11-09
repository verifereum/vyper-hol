(* Consumer boundary: the RHS frame keeps the preloaded current word's
   metadata, while ptr_val_ok supplies the RHS word's metadata directly. *)
Theory augAssignPtrOperandBoundary
Ancestors augAssignPtrRhsFrame bodyPtrDefs ptrDiscipline

Theorem augassign_operands_clean:
  ghost_kept cenv es sr G0 tn0 s0 G tn /\ not_fresh_at sr x /\
  op_prov G0 (Var x) = NONE /\ op_taint tn0 (Var x) = {} /\
  ptr_val_ok cx ty v rhs G tn s /\ is_word_type ty ==>
  op_prov G (Var x) = NONE /\ op_taint tn (Var x) = {} /\
  op_prov G rhs = NONE /\ op_taint tn rhs = {}
Proof
  simp[op_prov_def, ptr_val_ok_def] >>
  metis_tac[ghost_kept_old_operand]
QED
