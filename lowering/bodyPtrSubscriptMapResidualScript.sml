(*
 * RESIDUAL of bodyPtrSubscript's subscript_expr_ptr_ok: the base's mapping
 * judgment.  The pointer twin of S1's body_subscript_map_residual
 * (bodySubscriptMapResidual), which S1 admits too: body_expr_ptr_ok
 * describes only expressions expr_body_pre holds of, which an expression
 * naming a mapping is not, so the induction hypothesis on the base does not
 * give its expr_map_sim_ptr (nor, for a nested mapping, its inner keys'
 * judgments).  It follows once body_expr_ptr_ok gets a mapping half,
 * proved by the induction from the twins of S1's compile_toplevel_map_case
 * and compile_subscript_map_map_case.
 *
 * TOP-LEVEL:
 *   body_subscript_map_base_ptr
 *)
Theory bodyPtrSubscriptMapResidual
Ancestors
  bodyPtrSubscriptMapDefs bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

Theorem body_subscript_map_base_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es kt vt.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    place_type cenv e1 = MapPT kt vt ==>
    expr_map_sim_ptr d ctx PG func cenv cx ty e1 es
Proof
  (* RESIDUAL: held per argon ruling 2026-11-08, as S1 holds its twin *)
  cheat
QED
