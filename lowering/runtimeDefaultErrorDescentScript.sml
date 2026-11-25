(* Lift a one-layer default-expression error exclusion to the whole suffix. *)
Theory runtimeDefaultErrorDescent
Ancestors
  vyperAST vyperInterpreter vyperState whitelistCheckerConsts constSubst
  arithmetic list

Theorem default_eval_error_if_descent:
  (!ds st ee.
    EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds /\
    (!p c a b. MEM p ds /\ expr_size c < expr_size p /\
      runtime_constant_expr mods c /\ no_sha256_expr c ==>
      eval_expr cx c a <> (INR (Error err),b)) ==>
    eval_exprs cx ds st <> (INR (Error err),ee)) /\
  EVERY (runtime_constant_expr mods) ds /\ no_sha256_exprs ds ==>
  !st ee. eval_exprs cx ds st <> (INR (Error err),ee)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!e a b. runtime_constant_expr mods e /\ no_sha256_expr e ==>
    eval_expr cx e a <> (INR (Error err),b)` by
    (gen_tac >> completeInduct_on `expr_size e` >> rpt strip_tac >>
     `eval_exprs cx [e] a = (INR (Error err),b)` by
       simp[Once evaluate_def, bind_def] >>
     `eval_exprs cx [e] a <> (INR (Error err),b)` suffices_by simp[] >>
     qpat_assum `!ds st ee. _ ==> eval_exprs cx ds st <> _`
       (qspecl_then [`[e]`,`a`,`b`] irule) >>
     simp[no_sha256_expr_def] >> rpt strip_tac >>
     qpat_assum `!m. m < v ==> _` (qspec_then `expr_size c` mp_tac) >>
     simp[] >> disch_then (qspec_then `c` mp_tac) >> simp[]) >>
  rpt gen_tac >>
  qpat_assum `!ds st ee. _ ==> eval_exprs cx ds st <> _`
    (qspecl_then [`ds`,`st`,`ee`] mp_tac) >>
  simp[]
QED
