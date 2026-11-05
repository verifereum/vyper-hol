(* Independent operand certificates.  The admitted pointer leaf and MakeArray
   ancestors are permitted inherited assumptions; this theory does not import
   the membership case or the mutual body theorem. *)
Theory bodyPtrBopInOperands
Ancestors
  exprSimPtr bodyPtrMakeArray bodyPtrPreds bodyPtrDefs bodySim
  exprSimSource exprSimHyps exprSimHypsDefs vyperAST vyperTypeCallGraph

Theorem body_literal_ptr_ok:
  !cx ty l. body_expr_ptr_ok cx (Literal ty l)
Proof
  rpt gen_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Literal ty l) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  irule leaf_expr_sim_ptr >> simp[] >> goal_assum drule
QED

Theorem string_membership_operands_ptr_ok:
  !cx. body_exprs_ptr_ok cx
    [Literal (BaseT (StringT 1)) (StringL "a");
     Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
       (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
       [Literal (BaseT (StringT 1)) (StringL "a")]]
Proof
  gen_tac >> simp[body_exprs_ptr_ok_def, body_literal_ptr_ok] >>
  strip_tac >> irule make_array_expr_ptr_ok >>
  simp[body_exprs_ptr_ok_def, body_literal_ptr_ok]
QED
