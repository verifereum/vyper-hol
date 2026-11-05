(*
 * The pointer twin of exprSimMain's compile_expr_sim and
 * compile_expr_vv_sim: an expression with no internal call simulates with
 * the ghost, at every source state that meets expr_sim_pre.
 *
 * TOP-LEVEL:
 *   compile_expr_sim_ptr
 *)
Theory exprSimPtr
Ancestors
  bodyPtrDefs exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter list

(* ADMITTED: a piece of the body induction; bodySimPtrMain's
   body_expr_ptr_ok_intro uses it for the expressions without internal
   calls. *)
Theorem compile_expr_sim_ptr:
  !d PG ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  cheat
QED
