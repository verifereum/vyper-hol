(* Request-prefix companion to bodyFullForHandlers. *)
Theory s1PrefixForHandlers
Ancestors
  s1PrefixPreds bodyFullForHandlers s1PrefixDefs

val _ = Parse.hide "body";

Theorem for_body_cleanup_prefix:
  !DF lo d ctx func PG tops cx st0 body es s G tn Q R.
  es.scopes <> [] /\
  gas_outcome_full (DF,lo,d,ctx,func,PG) tops cx st0
    (eval_stmts cx body) (es,s,G,tn) Q R /\
  gas_prefix_full (DF,lo,d,ctx,func,PG)
      cx st0 (eval_stmts cx body)
      (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,d,ctx,func,PG)
      cx st0 (finally (try (do eval_stmts cx body; return F od)
       handle_loop_exception) pop_scope)
      (es,s,G,tn)
Proof
  cheat
QED
