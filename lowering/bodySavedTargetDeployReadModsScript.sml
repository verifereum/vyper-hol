(* The runtime checker artifact rules out deployment-only nested callees
   on the read-only path. Use the resulting frame at the saved RHS read. *)
Theory bodySavedTargetDeployReadMods
Ancestors
  bodySavedTargetSourceMods bodyInvSplit bodyCallSupport
  exprLowering vyperTypeContract vyperInterpreter option

Theorem saved_target_read_deploy_mods:
  contract_inv mods exps ctx cenv cx /\ cx.in_deploy /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
    (INL p,ee with gas_obs := tail)) /\
  read_result cx raw mid = (INL v,mid) ==>
  read_result cx raw ee = (INL v,ee)
Proof
  simp[IS_SOME_EXISTS] >> strip_tac >>
  drule_all saved_checked_target_source_update_mods >> simp[]
QED
