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
  cheat
QED
