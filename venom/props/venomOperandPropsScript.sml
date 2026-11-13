(*
 * eval_operands over appended and reversed operand lists.
 *
 * TOP-LEVEL:
 *   eval_operands_append  - operands of an append, as the two parts
 *   eval_operands_reverse - operands of a reversed list
 *)
Theory venomOperandProps
Ancestors
  venomState list

Theorem eval_operands_append:
  !xs ys s. eval_operands (xs ++ ys) s =
    OPTION_BIND (eval_operands xs s) (\vx.
      OPTION_BIND (eval_operands ys s) (\vy. SOME (vx ++ vy)))
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands xs s` >> simp[] >>
  Cases_on `eval_operands ys s` >> simp[]
QED

Theorem eval_operands_reverse:
  !xs s. eval_operands (REVERSE xs) s =
    OPTION_MAP REVERSE (eval_operands xs s)
Proof
  Induct >> simp[eval_operands_def, eval_operands_append] >> rpt gen_tac >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands xs s` >> simp[]
QED
