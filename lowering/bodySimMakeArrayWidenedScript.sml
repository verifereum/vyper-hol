(*
 * The body simulation of S1: an array literal with an element whose value
 * the lowering lays out differently from its type, for bodySimExprCases'
 * body_make_array_case.
 *
 * HELD for the posts-interface wave: its proof needs expr_post/vv_post to
 * describe a widened internal call's value at its lowered type
 * (post_value_type), which base 18f70e04a does not have.  The proof on that
 * interface is harvested on bot/opus/seq-1012-{ifexp-arm,aggr-elem}; it
 * lands with the interface after the sixteen frozen branches merge.  Not
 * open work here.
 *
 * TOP-LEVEL:
 *   body_make_array_widened_call_elem — that case
 *)

Theory bodySimMakeArrayWidened
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* As for body_struct_lit_widened_call_elem (bodySimStructLitWidened), for
   an array literal. *)
Theorem body_make_array_widened_call_elem:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_ok cx es) ==>
    !tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  cheat
QED

