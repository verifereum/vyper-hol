(* TOP-LEVEL: source_supply_action_create for funded creation and rollback.
 *)
Theory vyperSourceCreateSupply
Ancestors
  list pair option arithmetic vyperMisc vyperSourceSupplyDefs
  vyperSupplyBoundary vyperAdapterSupply vyperCreate vyperState
Libs
  pairLib

(* Account replacement after the EVM run uses the adapter's proved bound;
   the temporary funded prelude is never used as a fresh funding premise. *)
Theorem source_supply_action_create:
  source_supply_action (eval_create cx kind has_salt rof arg_tys values blueprint_size)
Proof
  simp[source_supply_action_def] >> qx_gen_tac `before` >> strip_tac >>
  `accounts_supply_bounded before.accounts` by fs[source_supply_def] >>
  simp_tac bool_ss [eval_create_def, LET_THM, bind_def, ignore_bind_def,
    get_accounts_def, get_transient_storage_def, get_pending_deletions_def,
    lift_option_type_def, check_def, assert_def, update_accounts_def,
    update_transient_def, update_pending_deletions_def, append_logs_def,
    create_soft_failure_def, return_def, raise_def, option_CASE_rator,
    prod_CASE_rator, COND_RATOR] >>
  rpt (BasicProvers.PURE_TOP_CASE_TAC >>
    gvs[return_def, raise_def, source_supply_def, evaluation_state_accfupds,
        accounts_supply_increment_nonce, accounts_supply_create_rollback,
        NOT_LESS, AllCaseEqs()]) >>
  drule_all (SRULE [] run_create_evm_supply) >> simp[]
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourceCreateSupply");
