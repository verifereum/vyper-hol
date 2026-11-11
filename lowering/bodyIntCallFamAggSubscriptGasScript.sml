(* Source gas queues do not participate in resource continuation frames.
   Resource and endpoint gas equalities are inherited from StructFields. *)
Theory bodyIntCallFamAggSubscriptGas
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggStructFields loweringPosts

Theorem intcall_expr_cont_initial_gas_obs[simp]:
  intcall_expr_cont fp ce env (es with gas_obs := gs) sa s ee sb u <=>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  simp[intcall_expr_cont_def, locals_kept_def]
QED
