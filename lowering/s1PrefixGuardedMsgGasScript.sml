(* Guarded request-prefix introduction for the GAS environment read. *)
Theory s1PrefixGuardedMsgGas
Ancestors
  s1PrefixPreds s1PrefixMsgGas exprBodyPreProps vyperAST vyperTypeSystem

Theorem body_msg_gas_prefix_case:
  !cx ann args.
    body_expr_prefix_ok cx (Builtin ann (Env MsgGas) args)
Proof
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >> rpt strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[compile_msg_gas_sim_prefix]
QED
