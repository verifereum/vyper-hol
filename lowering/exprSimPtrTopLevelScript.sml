(*
 * The pointer twin of S1's TopLevelName case: a storage, transient, immutable or constant read, which may copy into a fresh buffer.
 *
 * TOP-LEVEL:
 *   toplevel_expr_sim_ptr
 *)
Theory exprSimPtrTopLevel
Ancestors
  bodyPtrDefs exprSimHypsDefs vyperAST vyperInterpreter list

Theorem toplevel_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
Proof
  cheat
QED
