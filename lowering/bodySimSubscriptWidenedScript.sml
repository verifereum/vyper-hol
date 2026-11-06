(*
 * The body simulation of S1: a subscript whose base value the lowering
 * lays out differently from the base's type, for bodySimExprCases'
 * body_subscript_case.
 *
 * TOP-LEVEL:
 *   body_subscript_widened_call_base — that case
 *)

Theory bodySimSubscriptWidened
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* A subscript whose base value the lowering lays out differently from the
   base's type: an internal call whose callee's return type the call's type
   widens.  compile_subscript reads the base at offsets taken from the base's
   type (place_type), so for a tuple base this reads the wrong field until the
   subscript readers use the lowered layout. *)
Theorem body_subscript_widened_call_base:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ok cx e2) /\
    body_expr_ok cx e1 ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Subscript v8 e1 e2) es /\
      post_value_type cenv e1 <> expr_type e1 ==>
      expr_sim ctx func cenv cx ty (Subscript v8 e1 e2) es /\
      expr_vv_sim ctx func cenv cx ty (Subscript v8 e1 e2) es
Proof
  cheat
QED
