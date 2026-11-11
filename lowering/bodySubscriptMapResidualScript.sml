(*
 * RESIDUAL of the body simulation's subscript case (bodySimExprCases'
 * body_subscript_case): the base's mapping judgment at nocalls = F.
 *
 * compile_subscript_case takes expr_map_case of a mapping-typed base, but
 * body_expr_ok describes only expr_sim and expr_vv_sim, which say nothing
 * of an expression naming a mapping (expr_body_pre never holds of one), so
 * the induction hypothesis body_expr_ok cx e1 does not give it.  This is
 * admitted until body_expr_ok gets a mapping half (expr_map_pre ==>
 * expr_map_sim), proved by the induction from compile_toplevel_map_case and
 * compile_subscript_map_map_case (exprSimSubscriptMap), after which it
 * follows from body_expr_ok cx e1 directly.
 *)
Theory bodySubscriptMapResidual
Ancestors
  exprSimMapDefs bodySim exprLowering vyperInterpreter

Theorem body_subscript_map_residual:
  !cx e1 e2 tops ctx func cenv kt vt.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ok cx e2) /\
    body_expr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    place_type cenv e1 = MapPT kt vt ==>
    expr_map_case F ctx func cenv cx e1
Proof
  cheat
QED
