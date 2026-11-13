(*
 * The pointer twin of exprSimMain's compile_expr_sim and
 * compile_expr_vv_sim at the leaf expressions (names, top-level names,
 * flag members, literals): they simulate with the ghost at every source
 * state that meets expr_sim_pre.  bodySimPtrMain's induction takes every
 * other expression to its own case piece.
 *
 * TOP-LEVEL:
 *   leaf_expr_sim_ptr -- by constructor: exprSimPtrName,
 *     exprSimPtrTopLevel, exprSimPtrFlagMember, exprSimPtrLiteral
 *)
Theory exprSimPtr
Ancestors
  exprSimPtrName exprSimPtrTopLevel exprSimPtrFlagMember exprSimPtrLiteral
  bodyPtrDefs exprSimHyps exprSimHypsDefs vyperAST vyperInterpreter list

(* bodySimPtrMain's body_expr_ptr_ok_leaf uses it. *)
Theorem leaf_expr_sim_ptr:
  !d PG ctx func cenv cx env ty e es.
    ((?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
     (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l)) /\
    expr_sim_pre cenv cx env e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[name_expr_sim_ptr, toplevel_expr_sim_ptr,
            flag_member_expr_sim_ptr, literal_expr_sim_ptr]
QED
