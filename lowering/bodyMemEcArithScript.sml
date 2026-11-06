(* Memory case of the body induction (bodyMemory's body_mem_mutual): ecadd and
   ecmul. *)
Theory bodyMemEcArith
Ancestors
  bodyMemoryPreds bodyMemEcArithSimulation

Theorem body_ec_arith_mem_case:
  !cx ty bt es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `?a b. es = [a;b]` by
    metis_tac[exprSimECArithTheory.ec_pre_types] >> gvs[] >>
  irule ec_arith_sim_mem >>
  gvs[vyperContextTheory.builtin_args_length_ok_def] >> metis_tac[]
QED
