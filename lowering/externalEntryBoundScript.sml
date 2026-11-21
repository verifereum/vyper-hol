Theory externalEntryBound
Ancestors
  vyperInterpreter vyperContext vyperState finite_map

(* send_call_value reads and writes only accounts, so it runs the same
   under any scopes. *)
Theorem send_call_value_with_scopes:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.scopes = s.scopes /\
    !sc. send_call_value mut cx (s with scopes := sc) =
         (r, s' with scopes := sc)
Proof
  rw[send_call_value_def, transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, vyperStateTheory.return_def,
     vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[AllCaseEqs()]
QED

(* Likewise under any gas observations. *)
Theorem send_call_value_with_gas_obs:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.gas_obs = s.gas_obs /\
    !gs. send_call_value mut cx (s with gas_obs := gs) =
         (r, s' with gas_obs := gs)
Proof
  rw[send_call_value_def, transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, vyperStateTheory.return_def,
     vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[AllCaseEqs()]
QED

(* The source state where an external entry's binding is done, in
   call_external_function_trace's order: value moved, omitted defaults
   evaluated, arguments bound; before the nonreentrant lock. *)
Definition external_entry_bound_def:
  external_entry_bound tops am tx os gx mut args dflts es <=>
    ?s1 dflt_vs s2 env.
      send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am [FEMPTY] with
           <| outcomes := SOME os; requests := []; gas_obs := gx |>) =
        (INL (), s1) /\
      eval_external_defaults
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) s1 =
        (INL dflt_vs, s2) /\
      bind_arguments (type_env tops) args (tx.args ++ dflt_vs) = SOME env /\
      es = s2 with scopes := [env]
End

Theorem external_entry_bound_no_defaults:
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME os; requests := [] |>) =
    (INL (), es0) ==>
  !gx. external_entry_bound tops am tx os gx mut args [] (es0 with gas_obs := gx)
Proof
  strip_tac >> gen_tac >>
  drule send_call_value_with_scopes >> strip_tac >>
  pop_assum (qspec_then `[FEMPTY]` assume_tac) >>
  `send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [FEMPTY] with <| outcomes := SOME os; requests := [] |>) =
    (INL (), es0 with scopes := [FEMPTY])` by
    fs[initial_state_def] >>
  drule send_call_value_with_gas_obs >> strip_tac >>
  pop_assum (qspec_then `gx` mp_tac) >>
  simp[external_entry_bound_def, initial_state_def] >>
  strip_tac >> fs[initial_state_def, evaluation_state_component_equality]
QED
