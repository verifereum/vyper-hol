(* Deployment supplies the installed code and the source premises of a
 * subsequent call to the same linked contract. *)
Theory e2eModsLifecycle
Ancestors
  e2eLifecycle e2eModsDefs e2eDeployModsDefs e2eDefs e2eComposition
  vyperContext vyperInterpreter vyperState vyperTypeContract
  vyperTypeContractSoundness vyperTypeDeploymentMachine
  vyperTypeInitialState vyperTypeInvariants vyperDeployConstantsFoldMods
  vfmState vfmExecution vfmRunCall vfmTotalBalance callTrace
  alist finite_map

Definition call_ready_mods_def:
  call_ready_mods mods exps runtime_bc am a <=>
    am.logs = [] /\ am.pending_deletions = [] /\
    installed_code_rel_mods mods runtime_bc (account_immutables am a)
      (lookup_account a am.accounts).code /\
    !tx. tx.target = a /\ call_tx_well_typed tx ==>
         source_typing_ok_mods mods exps am tx /\
         source_deployment_rel_mods mods exps am tx
End

Theorem call_ready_mods_singleton:
  call_ready_mods [(NONE, tops)] [] = call_ready tops
Proof
  simp[FUN_EQ_THM, call_ready_mods_def, call_ready_def,
       installed_code_rel_mods_singleton, source_typing_ok_mods_singleton,
       source_deployment_rel_mods_singleton]
QED

Triviality deployed_sources_layouts:
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  am'.sources <> am.sources ==>
  am'.sources = (tx.target, mods) :: am.sources /\ am'.layouts = am.layouts
Proof
  strip_tac >>
  drule_all load_contract_success_constructor_constants_context >>
  strip_tac >>
  drule call_external_function_preserves_sources >> simp[]
QED

Triviality deploy_typing_mods_checker:
  deploy_typing_ok_mods mods exps am tx ==>
  ?deploy_art runtime_art.
    check_contract T am.layouts tx.target mods = SOME deploy_art /\
    check_contract F am.layouts tx.target mods = SOME runtime_art /\
    exports_ok am.layouts tx.target mods exps /\
    machine_well_typed am /\ call_tx_well_typed tx
Proof
  simp[deploy_typing_ok_mods_def] >> metis_tac[]
QED

Triviality deploy_typing_mods_ownership:
  deploy_typing_ok_mods mods exps am tx ==>
  linked_state_ownership_ok am.layouts tx.target mods exps
Proof
  simp[deploy_typing_ok_mods_def] >> metis_tac[]
QED

Triviality layouts_agree_mods_cong:
  am2.layouts = am1.layouts /\ tx2.target = tx1.target ==>
  (layouts_agree_mods mods exps am2 tx2 <=> layouts_agree_mods mods exps am1 tx1)
Proof
  simp[layouts_agree_mods_def]
QED

Triviality deployed_global_cells_typed:
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  am'.sources <> am.sources /\
  ALOOKUP am'.sources tx.target = SOME mods /\
  check_contract F am'.layouts tx.target mods = SOME art ==>
  global_cells_typed_mods mods art.cta_bare_globals (account_immutables am' tx.target)
Proof
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`call_tx` |-> `deploy_tx`]
    load_contract_establishes_immutables_ready)) >>
  simp[immutables_ready_def, get_tenv_def, initial_evaluation_context_def,
       account_immutables_def, empty_immutables_def, global_cells_typed_mods_def] >>
  metis_tac[optionTheory.IS_SOME_EXISTS, pairTheory.PAIR]
QED

Theorem deploy_establishes_call_ready_mods:
  deploy_typing_ok_mods mods exps am tx /\
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  deploy_result_rel_mods H mods runtime_bc tx es r es' (INL (am', rqs)) ==>
  call_ready_mods mods exps runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  drule deploy_typing_mods_checker >> strip_tac >>
  drule deploy_typing_mods_ownership >> strip_tac >>
  `wf_state es /\ ALOOKUP am.sources tx.target = NONE /\
   ALOOKUP mods NONE <> NONE /\ layouts_agree_mods mods exps am tx` by
    fs[deploy_state_rel_mods_def] >>
  `am'.sources <> am.sources` by (strip_tac >> gvs[deploy_result_rel_mods_def]) >>
  drule_all deployed_sources_layouts >> strip_tac >>
  `?main. ALOOKUP mods NONE = SOME main` by
    (Cases_on `ALOOKUP mods NONE` >> gvs[]) >>
  `context_well_typed
     (initial_evaluation_context ((tx.target, mods) :: am.sources)
        am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    fs[context_well_typed_def, initial_evaluation_context_def, call_tx_well_typed_def] >>
  drule_all load_contract_establishes_machine_well_typed >> strip_tac >>
  drule_all load_contract_establishes_constants_fold_mods >> strip_tac >>
  drule load_contract_deployed_exports >> strip_tac >>
  `accounts_well_typed es'.rollback.accounts` by
    (irule run_call_accounts_well_typed >> goal_assum $ drule_at Any >> simp[]) >>
  `machine_well_typed (next_source_machine am' es')` by
    (irule next_source_machine_well_typed >> fs[machine_well_typed_def]) >>
  `global_cells_typed_mods mods runtime_art.cta_bare_globals
     (account_immutables am' tx.target)` by
    (irule deployed_global_cells_typed >> simp[] >>
     qexistsl [`am`, `exps`, `gs`, `orc`, `rqs`] >> simp[]) >>
  simp[call_ready_mods_def] >> conj_tac
  >- (gvs[deploy_result_rel_mods_def, installed_code_rel_mods_def,
          lookup_account_process_deletions] >> metis_tac[]) >>
  qx_gen_tac `call_tx` >> strip_tac >>
  `layouts_agree_mods mods exps (next_source_machine am' es') call_tx` by
    metis_tac[layouts_agree_mods_cong, next_source_machine_fields] >>
  conj_tac
  >- gvs[Once source_typing_ok_mods_def, account_immutables_def] >>
  fs[source_deployment_rel_mods_def]
QED

Theorem deploy_call_result_establishes_call_ready_mods:
  deploy_typing_ok_mods mods exps am tx /\
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  deploy_call_result_rel_mods mods exps runtime_bc am tx es r es' ==>
  gas_readings_rel (gas_readings es)
    (\gs. deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace es)) gs ==>
          !am' rqs.
            load_contract (SOME (MAP SND (call_trace es))) gs am tx
              mods exps = INL (am', rqs) ==>
            call_ready_mods mods exps runtime_bc (next_source_machine am' es')
              tx.target)
Proof
  rw[deploy_call_result_rel_mods_def] >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  rw[] >> irule (INST_TYPE [alpha |-> “:256”] deploy_establishes_call_ready_mods) >>
  rpt (conj_tac >- simp[]) >>
  qexistsl_tac [`storage_trace_horizon (deploy_storage_trace_mods
                   (SOME (MAP SND (call_trace es))) gs am tx mods exps)`,
                `am`, `deploy_bc`, `es`, `gs`, `SOME (MAP SND (call_trace es))`,
                `r`, `rqs`] >>
  gvs[]
QED
