(*
 * The external-call case of the full body induction: target, positional
 * arguments and keyword arguments over the finite-horizon joint judgment.
 *
 * Admitted until its providers (the S1 extcall seams, bodyMemExtCall,
 * exprSimExtCallCase and the external-call gas shadow) are on the
 * finite-horizon base.
 *
 * TOP-LEVEL:
 *   extcall_expr_full_ok
 *)
Theory bodyFullExtCall
Ancestors
  bodyFullPreds vyperInterpreter vyperAST list

val _ = Parse.hide "body";

Theorem extcall_expr_full_ok:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_full_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_full_ok cx (TAKE 1 es) ==>
    body_expr_full_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED
