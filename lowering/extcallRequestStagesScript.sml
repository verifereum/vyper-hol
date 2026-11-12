(* Source-order boundary for external request construction. *)
Theory extcallRequestStages
Ancestors
  exprSimExtCallCase exprSimWordArgs vyperInterpreter vyperState list rich_list

Theorem extcall_request_source_cons:
  eval_expr cx (Call ann (ExtCall stat skip (fname,ats,rt) opts)
    (h::rest) dflt) =
  do tv <- eval_expr cx h;
     target <- read_result cx tv;
     rs <- eval_expr_results cx (TAKE (LENGTH ats) rest);
     kwargs <- eval_exprs cx (DROP (LENGTH ats) rest);
     vs <- read_results cx rs;
     eval_ext_call cx stat skip (fname,ats,rt) opts
       (target::(vs ++ kwargs))
  od
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[eval_extcall_stages, eval_exprs_cons_action,
       bind_assoc, bind_return]
QED
