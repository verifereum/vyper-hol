Theory ctorDeployMemoryRunMemPrefixSource
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs vyperTypeEntryReadiness
  vyperInterpreter vyperState vyperContext e2eDefs finite_map option

Theorem ctor_prefix_singleton_type_env:
  type_env_all_modules [(NONE,tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

Theorem ctor_prefix_send_value_success:
  value_transfer_ok tx am.accounts /\
  evaluate_all_constants (deploy_evaluation_context tops am tx)
    (am with <| immutables updated_by CONS (tx.target, imms);
                exports updated_by CONS (tx.target, []) |>)
    tx.target [(NONE,tops)] = SOME am_c /\
  (mut = Payable \/ tx.value = 0) ==>
  ?s. send_call_value mut (deploy_evaluation_context tops am tx)
    (initial_state am_c [env] with <| outcomes := NONE; requests := [] |>) =
    (INL (),s)
Proof
  strip_tac >> drule evaluate_all_constants_preserves_accounts >> strip_tac >>
  gvs[send_call_value_def, deploy_evaluation_context_def,
      initial_evaluation_context_def, value_transfer_ok_def,
      transfer_value_def, initial_state_def, get_accounts_def,
      update_accounts_def, bind_def, ignore_bind_def, return_def,
      check_def, vyperStateTheory.assert_def, raise_def] >>
  Cases_on `tx.value = 0` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.bind_def,
      vyperStateTheory.assert_def, vyperStateTheory.raise_def] >>
  Cases_on `tx.sender = tx.target` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.bind_def,
      vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
      vyperStateTheory.update_accounts_def]
QED

Theorem ctor_prefix_source_start_if:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,fbody) /\
  (mut = Payable \/ tx.value = 0) ==>
  ?am_c es0. deploy_ctor_start tops am tx (mut,F,fbody,am_c,es0)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gns[deploy_source_ok_def, deploy_typing_ok_def, deploy_state_rel_def,
      constructor_args_encode_def] >>
  qpat_x_assum `supported_program _ /\ _` strip_assume_tac >>
  qpat_x_assum `?ctxt rb args_bytes. _` strip_assume_tac >>
  drule checked_deployment_constants_ready_setup >> strip_tac >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env`
    by metis_tac[IS_SOME_EXISTS] >>
  `?s. send_call_value mut (deploy_evaluation_context tops am tx)
      (initial_state am_c [env] with <| outcomes := NONE; requests := [] |>) =
      (INL (),s)` by (irule ctor_prefix_send_value_success >> simp[] >>
        qexists_tac `imms` >> simp[]) >>
  qexistsl [`am_c`, `s`] >>
  simp[deploy_ctor_start_def, ctor_prefix_singleton_type_env,
       lock_if_nr_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.bind_def] >>
  metis_tac[]
QED

Theorem ctor_prefix_source_obstruction:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  (!mut nr fbody am_c es0.
    ~deploy_ctor_start tops am tx (mut,nr,fbody,am_c,es0)) ==>
  ?mut args fbody.
    vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
      SOME (mut,F,args,[],NoneT,fbody) /\
    mut <> Payable /\ tx.value <> 0
Proof
  rpt strip_tac >>
  `?mut args fbody.
    vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
      SOME (mut,F,args,[],NoneT,fbody)` by
    (qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
     simp[deploy_state_rel_def, constructor_args_encode_def] >> metis_tac[]) >>
  qexistsl [`mut`, `args`, `fbody`] >> simp[] >>
  metis_tac[ctor_prefix_source_start_if]
QED
