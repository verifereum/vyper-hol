(* Piece of bodySimCallCases.body_extcall_case. *)

Theory bodySimCallExtcall
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): external calls.  Its case lemma is
   still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem extcall_body_expr_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ok cx (TAKE 1 es) ==>
    body_expr_ok cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED
