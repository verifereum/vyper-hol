(* Memory case of the body induction (bodyMemory's body_mem_mutual): external
   call. *)
Theory bodyMemExtCall
Ancestors
  bodyMemoryPreds

Theorem body_extcall_mem_case:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_mem_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_mem_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_mem_ok cx (TAKE 1 es) ==>
    body_expr_mem_ok cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED
