(*
 * The body simulation of S1: in and not in on an array literal of words
 * (#636 operands with internal calls).  Its lowering compiles each element
 * (exprSimBopInLiteralWord), so this takes the elements' judgments.  The
 * induction hypotheses give the array's only; bodySimBopHeld's
 * body_make_array_children_ok extracts the elements' from it.
 *
 * TOP-LEVEL:
 *   body_expr_ok_case  — body_expr_ok gives the shared judgments at
 *                        nocalls = F in every frame
 *   body_exprs_ok_case — body_exprs_ok is exprs_case at nocalls = F
 *   body_bop_in_literal_word_case — that case, by exprSimBopInLiteralWord's
 *                        compile_bop_in_literal_word_case
 *)

Theory bodySimBopInLiteralWord
Ancestors
  exprSimBopInLiteralWord exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

Theorem body_expr_ok_case:
  !cx e tops ctx func cenv.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx ==>
    expr_sim_case F ctx func cenv cx e /\ expr_vv_case F ctx func cenv cx e
Proof
  rw[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

Theorem body_exprs_ok_case:
  !cx es tops ctx func cenv.
    body_exprs_ok cx es /\ body_inv tops ctx cenv cx ==>
    exprs_case F ctx func cenv cx es
Proof
  gen_tac >> Induct >> rw[body_exprs_ok_def, exprs_case_def] >>
  metis_tac[body_expr_ok_case]
QED

Theorem body_bop_in_literal_word_case:
  !cx ty bop e1 a t n elems.
    is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\ body_expr_ok cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
     body_exprs_ok cx elems) ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt strip_tac >> simp[body_expr_ok_def] >> rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok (MakeArray t n) (LENGTH elems)` by
    (gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
     qpat_x_assum `well_typed_builtin_app a _ _`
       (mp_then Any mp_tac
          vyperTypeBuiltinsTheory.well_typed_builtin_app_length) >>
     simp[]) >>
  `exprs_case F ctx func cenv cx (e1::elems)` by
    (simp[exprs_case_def] >> rpt conj_tac
     >- metis_tac[body_expr_ok_case] >- metis_tac[body_expr_ok_case] >>
     rpt strip_tac >> irule body_exprs_ok_case >> metis_tac[]) >>
  `expr_sim_case F ctx func cenv cx
     (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems]) /\
   expr_vv_case F ctx func cenv cx
     (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])` by
    (irule compile_bop_in_literal_word_case >> simp[]) >>
  fs[expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED
