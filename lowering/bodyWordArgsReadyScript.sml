Theory bodyWordArgsReady
Ancestors
  bodySimMain bodySimExprCases exprSimPrecompiles exprSimHypsDefs
  bodySim exprSimHypsDefs list

(* Source readiness is supplied by the independent S1 induction, not by
   dropping the extra entry assumptions of the pointer judgment. *)
Theorem body_word_args_ready:
  body_inv tops ctx cenv cx /\
  (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) ==>
  typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  strip_tac >>
  `exprs_case F ctx func cenv cx args` by
    metis_tac[body_sim_mutual, body_exprs_ok_case] >>
  irule typed_args_ready_of_case >> qexists_tac `F` >> simp[] >> metis_tac[]
QED
