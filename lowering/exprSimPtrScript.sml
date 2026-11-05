(*
 * The pointer twin of exprSimMain's compile_expr_sim and
 * compile_expr_vv_sim at the leaf expressions (names, top-level names,
 * flag members, literals): they simulate with the ghost at every source
 * state that meets expr_sim_pre.  bodySimPtrMain's induction takes every
 * other expression to its own case piece.
 *
 * TOP-LEVEL:
 *   leaf_expr_sim_ptr
 *)
Theory exprSimPtr
Ancestors
  bodyPtrDefs exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter list

(* ADMITTED: a piece of the body induction; bodySimPtrMain's
   body_expr_ptr_ok_leaf uses it. *)
Theorem leaf_expr_sim_ptr:
  !d PG ctx func cenv cx env ty e es.
    ((?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
     (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l)) /\
    expr_sim_pre cenv cx env e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  cheat
QED
