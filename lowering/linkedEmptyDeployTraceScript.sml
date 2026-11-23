(* Source execution of the synthetic empty deployment constructor. *)
Theory linkedEmptyDeployTrace
Ancestors
  e2eDeployModsDefs e2eDeployDefs e2eDefs ctorDeployLoweringNoCtor vyperConstantsStorageFrame
  vyperInterpreter vyperContext vyperState compileUnit finite_map alist list pair
Theorem load_contract_empty_ctor_trace:
  vyperInterpreter$lookup_function NONE "__init__" Deploy (main_module mods) =
    SOME (Payable,F,[],[],NoneT,[]) /\
  tx.function_name = "__init__" /\ tx.args = [] /\
  value_transfer_ok tx am.accounts /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_module_constants_trace (deploy_evaluation_context_mods mods am tx)
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target (constants_order mods) = (SOME am_c,[]) ==>
  !orc gs. load_contract_trace orc gs am tx mods exps =
    (INL (finalize_pending_deletions
      (am_c with <|accounts := accounts_after_transfer tx am.accounts;
                   sources updated_by CONS (tx.target,mods)|>),[]),[])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  qabbrev_tac `cx = deploy_evaluation_context_mods mods am tx` >>
  qabbrev_tac `installed = am with <|immutables updated_by CONS (tx.target,imms);
      exports updated_by CONS (tx.target,exps)|>` >>
  `cx.in_deploy /\ cx.txn = tx with created_in_tx := T` by
    simp[Abbr `cx`, deploy_evaluation_context_mods_def, initial_evaluation_context_def] >>
  `evaluate_all_constants cx installed tx.target mods = SOME am_c` by
    simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
  `am_c.accounts = am.accounts` by
    (drule evaluate_all_constants_machine_frame >>
     disch_then (mp_tac o Q.AP_TERM `\m. m.accounts`) >>
     simp[Abbr `installed`]) >>
  qabbrev_tac `st = initial_state am_c [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gs; storage_trace := []|>` >>
  `value_transfer_ok cx.txn st.accounts` by
    simp[Abbr `st`, initial_state_def, value_transfer_created_in_tx] >>
  qpat_assum `Abbrev (st = _)` (fn initial =>
    qpat_assum `am_c.accounts = am.accounts` (fn accounts =>
      drule_then (assume_tac o SIMP_RULE (srw_ss())
        [REWRITE_RULE [markerTheory.Abbrev_def] initial, initial_state_def, accounts])
        no_ctor_send_value)) >>
  `call_external_function_trace orc gs installed cx F Payable (main_module mods)
      mods [] [] [] [] NoneT =
    (INL NoneV, am_c with accounts := accounts_after_transfer tx am.accounts, [], [])` by
    simp[call_external_function_trace_def, GSYM markerTheory.Abbrev_def,
         bind_arguments_def, eval_external_defaults_nil,
         lock_if_nr_def, unlock_if_nr_def, is_view_mut_def,
         bind_def, ignore_bind_def, return_def, set_scopes_def, evaluate_def,
         abstract_machine_from_state_def, abstract_machine_component_equality,
         Abbr `st`, initial_state_def, value_transfer_created_in_tx] >>
  qpat_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Abbr `cx`, Abbr `installed`, load_contract_trace_def, main_module_def,
       deploy_evaluation_context_mods_def, initial_evaluation_context_def] >>
  Cases_on `ALOOKUP mods NONE` >>
  qpat_assum `tx.function_name = "__init__"` (fn nm =>
    fs[nm, main_module_def, deploy_evaluation_context_mods_def, initial_evaluation_context_def])
QED
