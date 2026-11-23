(* Advance a checked linked constructor to its bound source body. *)
Theory linkedConstructorSourceTrace
Ancestors
  ctorDeployLoweringArms ctorDeployLoweringEntrySourceFrame
  vyperTypeDeploymentSoundness vyperConstantsStorageFrame sourceValueRejection
  e2eDeployModsDefs e2eDeployDefs e2eDefs vyperInterpreter vyperState
  vyperContext vyperValue vyperCall list alist finite_map pair

Theorem linked_constructor_source_trace:
  check_contract T am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\ tx.function_name = "__init__" /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,src_body) /\
  bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
  value_transfer_ok tx am.accounts /\ (mut = Payable \/ tx.value = 0) ==>
  ?imms am0 am_c es0.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    am0 = (am with <|immutables updated_by CONS (tx.target,imms);
      exports updated_by CONS (tx.target,exps)|>) /\
    evaluate_module_constants_trace (deploy_evaluation_context_mods mods am tx)
      am0 tx.target (constants_order mods) = (SOME am_c,[]) /\
    am_c = (am0 with immutables := am_c.immutables) /\
    es0 = (initial_state am_c [scope] with
      accounts := accounts_after_transfer tx am.accounts) /\
    (!orc gs res st.
      eval_stmts (deploy_evaluation_context_mods mods am tx) src_body
        (es0 with <|outcomes := orc; gas_obs := gs|>) = (res,st) ==>
      load_contract_trace orc gs am tx mods exps =
        ((case res of
           INR HaltException =>
             INL (finalize_pending_deletions
               (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st),
               st.requests)
         | INR (ReturnException v) =>
             (case safe_cast NoneTV v of
                NONE => INR (Error (TypeError "ext cast ret"))
              | SOME _ => INL (finalize_pending_deletions
                  ((abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st)
                    with sources updated_by CONS (tx.target,mods)), st.requests))
         | INR exc => INR exc
         | INL () =>
             INL (finalize_pending_deletions
               ((abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st)
                 with sources updated_by CONS (tx.target,mods)), st.requests)),
         st.storage_trace))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choose_then `imms` assume_tac) check_contract_initial_immutables >>
  qabbrev_tac `am0 = am with <|immutables updated_by CONS (tx.target,imms);
                              exports updated_by CONS (tx.target,exps)|>` >>
  qabbrev_tac `cx = deploy_evaluation_context_mods mods am tx` >>
  `cx.in_deploy /\ cx.txn = (tx with created_in_tx := T) /\
   ALOOKUP cx.sources cx.txn.target = SOME mods /\
   ALOOKUP am0.immutables cx.txn.target = SOME imms` by
    simp[Abbr `cx`, Abbr `am0`, deploy_evaluation_context_mods_def,
         initial_evaluation_context_def] >>
  drule_all check_contract_evaluate_all_constants_trace >>
  qpat_assum `cx.txn = _` (fn txn =>
    disch_then (qx_choose_then `am_c` (assume_tac o SIMP_RULE (srw_ss()) [txn]))) >>
  `evaluate_all_constants cx am0 tx.target mods = SOME am_c` by
    simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
  `am_c = (am0 with immutables := am_c.immutables)` by
    (drule_then ACCEPT_TAC evaluate_all_constants_machine_frame) >>
  `am_c.accounts = am.accounts` by
    (qpat_assum `am_c = (am0 with immutables := _)`
       (mp_tac o Q.AP_TERM `\machine. machine.accounts`) >>
     simp[Abbr `am0`]) >>
  qabbrev_tac `es0 = initial_state am_c [scope] with
                    accounts := accounts_after_transfer tx am.accounts` >>
  qexistsl_tac [`imms`,`am0`,`am_c`,`es0`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `am0`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `es0`] >>
  rpt gen_tac >> disch_tac >>
  qabbrev_tac `entry = initial_state am_c [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gs; storage_trace := []|>` >>
  `value_transfer_ok cx.txn entry.accounts` by
    simp[Abbr `entry`, initial_state_def, value_transfer_created_in_tx] >>
  `?paid. send_call_value mut cx entry = (INL (),paid)` by
    (Cases_on `send_call_value mut cx entry` >> Cases_on `q` >>
     simp[] >>
     drule send_call_value_reject_iff >> simp[] >> metis_tac[]) >>
  `paid = (entry with accounts := accounts_after_transfer tx am.accounts)` by
    (drule_then assume_tac deploy_ctor_send_value_frame >>
     `paid.accounts = accounts_after_transfer tx am.accounts` by
       (qpat_assum `send_call_value mut cx entry = (INL (),paid)`
          (mp_tac o MATCH_MP deploy_ctor_send_value_accounts) >>
        simp[Abbr `entry`, initial_state_def, accounts_after_transfer_def]) >>
     qpat_assum `paid = (entry with accounts := paid.accounts)`
       (fn frame => ONCE_REWRITE_TAC [frame]) >>
     qpat_assum `paid.accounts = _` SUBST1_TAC >> REFL_TAC) >>
  `set_scopes [scope] paid =
    (INL (),es0 with <|outcomes := orc; gas_obs := gs|>)` by
    simp[Abbr `entry`, Abbr `es0`, set_scopes_def, return_def, initial_state_def] >>
  `LENGTH tx.args = LENGTH args` by (drule bind_arguments_length >> simp[]) >>
  qpat_assum `tx.function_name = "__init__"`
    (fn name => qpat_assum `ALOOKUP mods NONE = SOME tops` (fn main =>
      qpat_assum `initial_immutables _ mods = SOME imms` (fn initial =>
        qpat_assum `vyperInterpreter$lookup_function NONE "__init__" Deploy tops = _`
          (fn ctor => simp_tac (srw_ss()) [load_contract_trace_def, name, main,
            initial, ctor, LET_THM])))) >>
  `initial_evaluation_context ((tx.target,mods)::am.sources)
     am.layouts (tx with created_in_tx := T) NONE with in_deploy := T = cx` by
    simp[Abbr `cx`, deploy_evaluation_context_mods_def] >>
  simp[GSYM markerTheory.Abbrev_def] >>
  simp[call_external_function_trace_def, LET_THM, GSYM markerTheory.Abbrev_def] >>
  `(am with <|exports updated_by CONS (tx.target,exps);
               immutables updated_by CONS (tx.target,imms)|>) = am0` by
    simp[Abbr `am0`, abstract_machine_component_equality] >>
  qpat_assum `(am with <|exports updated_by _; immutables updated_by _|>) = am0`
    SUBST1_TAC >>
  qpat_assum `evaluate_module_constants_trace cx am0 _ _ = _`
    (fn constants => simp_tac (srw_ss()) [constants]) >>
  `set_scopes [scope] (entry with accounts := accounts_after_transfer tx am.accounts) =
    (INL (),es0 with <|outcomes := orc; gas_obs := gs|>)` by
    simp[Abbr `entry`, Abbr `es0`, set_scopes_def, return_def, initial_state_def] >>
  qpat_assum `send_call_value mut cx entry = _` (fn send =>
    qpat_assum `bind_arguments _ args tx.args = SOME scope` (fn binds =>
      simp_tac (srw_ss()) [bind_def, ignore_bind_def, eval_external_defaults_nil,
        return_def, send, binds])) >>
  qpat_assum `set_scopes [scope] (entry with accounts := _) = _` SUBST1_TAC >>
  simp[lock_if_nr_def, return_def] >>
  qpat_assum `eval_stmts cx src_body _ = (res,st)` SUBST1_TAC >>
  Cases_on `res`
  >- (Cases_on `x` >> simp[unlock_if_nr_def, return_def]) >>
  Cases_on `y` >> simp[NoAsms, unlock_if_nr_def, return_def, evaluate_type_def] >>
  Cases_on `safe_cast NoneTV v` >>
  qpat_assum `safe_cast NoneTV v = _` (fn cast => simp[NoAsms, cast])
QED
