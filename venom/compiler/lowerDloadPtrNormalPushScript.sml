Theory lowerDloadPtrNormalPush
Ancestors lowerDloadPtrInvoke lowerDloadPtrAggregate pred_set

(* Interface probe for the active set delivered by actual invoke. *)
Theorem dload_invoke_active_set_probe[local]:
  dload_boundary_core lo fs {a | ~retpc_var callee a} Ws
    PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs
    (set (fn_ir_vars callee) DIFF {a | retpc_var callee a}) Ws
    PG PH G H tn un s t cs ds
Proof
  strip_tac >> irule dload_boundary_vars_restrict >>
  goal_assum (drule_at Any) >> simp[SUBSET_DEF]
QED
