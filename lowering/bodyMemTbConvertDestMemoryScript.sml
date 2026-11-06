(* Store bounds for pointer-valued convert results. *)
Theory bodyMemTbConvertDestMemory
Ancestors exprSimMemDefs

Theorem convert_vv_store_bound_stack_capacity:
  expr_store_bound cx t v op s /\
  (!tvt w. evaluate_type (get_tenv cx) lt = SOME tvt /\
           eval_operand op s = SOME w ==>
           type_memory_size tvt = 0 \/
           w2n w + type_memory_size tvt <= s.vs_alloca_next) ==>
  vv_store_bound cx t lt ee (Value v) (StackValue t' op) s
Proof
  rw[vv_store_bound_def, expr_store_bound_def,
     vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
