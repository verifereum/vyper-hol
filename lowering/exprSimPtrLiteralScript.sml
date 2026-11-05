(*
 * The pointer twin of S1's Literal case: a word literal as a constant, a bytes or string literal written into a fresh buffer.
 *
 * TOP-LEVEL:
 *   literal_expr_sim_ptr
 *)
Theory exprSimPtrLiteral
Ancestors
  bodyPtrDefs exprSimHypsDefs vyperAST vyperInterpreter list

Theorem literal_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Literal ann l) es
Proof
  cheat
QED
