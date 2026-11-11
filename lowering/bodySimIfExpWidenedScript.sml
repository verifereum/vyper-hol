(*
 * The body simulation of S1: a ternary with an arm whose value the lowering
 * lays out differently from its source type, for bodySimExprCases'
 * body_ifexp_case.
 *
 * HELD for the posts-interface wave: its proof needs expr_post/vv_post to
 * describe a widened internal call's value at its lowered type
 * (post_value_type), which base 18f70e04a does not have.  The proof on that
 * interface is harvested on bot/opus/seq-1012-{ifexp-arm,aggr-elem}; it
 * lands with the interface after the sixteen frozen branches merge.  Not
 * open work here.
 *
 * TOP-LEVEL:
 *   body_ifexp_widened_call_arm — that case
 *)

Theory bodySimIfExpWidened
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* A ternary with an arm whose value the lowering lays out differently from
   its source type: an internal call whose callee's return type the call's
   type widens (supported_pure_expr keeps calls out of supported ternaries,
   but body_expr_ok ranges over every expression).  The arm's simulation
   would have to describe its value at the lowered type, which expr_sim
   does not do yet; that is the internal-call simulation's work, as for
   body_intcall_case. *)
Theorem body_ifexp_widened_call_arm:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e3) /\
    body_expr_ok cx e1 ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es /\
      (?e. (e = e2 \/ e = e3) /\
           ~((int_calls_expr e = [] \/
              same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
             post_value_type cenv e = expr_type e)) ==>
      expr_sim ctx func cenv cx ty (IfExp v5 e1 e2 e3) es /\
      expr_vv_sim ctx func cenv cx ty (IfExp v5 e1 e2 e3) es
Proof
  cheat
QED

