Theory vyperCall

Ancestors
  vyperInterpreter

Theorem eval_expr_intcall_drv:
  ∀cx ty nsid es drv.
    eval_expr cx (Call ty (IntCall nsid) es drv) =
    eval_expr cx (Call ty (IntCall nsid) es NONE)
Proof
  rpt gen_tac >>
  PairCases_on `nsid` >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
  simp[]
QED

Theorem bind_arguments_length:
  ∀tenv args vs env.
    bind_arguments tenv args vs = SOME env ⇒ LENGTH args = LENGTH vs
Proof
  Induct_on `args` >> simp[bind_arguments_def] >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[bind_arguments_def] >>
  Cases_on `evaluate_type tenv h'1` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv args t` >> simp[] >>
  strip_tac >> res_tac
QED
