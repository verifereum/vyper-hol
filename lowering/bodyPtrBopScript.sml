(*
 * Binary operators other than in and not in.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   bop_expr_ptr_ok
 *)
Theory bodyPtrBop
Ancestors
  bodyPtrBopBody bodyPtrBopResidual exprSimOperators compileEnv
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem bop_expr_ptr_ok:
  !cx ty bop es.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >> drule expr_body_pre_bop_args >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e1;e2]` by
    fs[vyperContextTheory.builtin_args_length_ok_def] >>
  Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)`
  >- (`body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])` by
        (irule bop_bytestring_expr_ptr_residual >> simp[]) >>
      fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  `body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])` by
    (irule bop_nonresidual_pair_ptr_ok >> simp[] >> metis_tac[]) >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED
