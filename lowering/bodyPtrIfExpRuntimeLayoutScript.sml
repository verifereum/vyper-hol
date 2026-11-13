Theory bodyPtrIfExpRuntimeLayout
Ancestors
  exprSimHyps exprSimHypsDefs

(* expr_sim_inv_memory_size is already the general recursive size bridge.
   It applies to every evaluated child, including named structs, without a
   value-typing or supported_expr premise. *)
Theorem ifexp_equal_compiler_runtime_sizes:
  !ce cx env es st dt sv dv.
    expr_sim_inv ce cx env es /\
    evaluate_type (get_tenv cx) st = SOME sv /\
    evaluate_type (get_tenv cx) dt = SOME dv /\
    type_memory_bytes ce st = type_memory_bytes ce dt ==>
    type_memory_size sv = type_memory_size dv
Proof
  rpt strip_tac >>
  metis_tac[expr_sim_inv_memory_size]
QED
