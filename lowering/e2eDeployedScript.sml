(* Single-module compiler headlines with a deployment-to-call handoff. *)
Theory e2eDeployed
Ancestors
  e2eDefs e2eDeployDefs e2eLifecycle e2eComposition
  e2eCorrectness e2eDeployCorrectness[qualified,ignore_grammar]
  e2eGasSufficientTop[qualified,ignore_grammar]
  compileVyper asmOptimizer vyperTypeContractSoundness
  immutableSectionRel vfmState vfmRunCall callTrace frameOutcome frameGas
  vyperInterpreter vyperStorageFootprint

(* Deployment installs the code and establishes the source facts at a.
   The transaction quantifier lets us reuse the existing source relations. *)
Definition deployed_def:
  deployed tops runtime_bc am a <=>
    installed_code_rel tops runtime_bc (account_immutables am a)
      (lookup_account a am.accounts).code /\
    !tx. tx.target = a /\ call_tx_well_typed tx ==>
         source_typing_ok tops am tx /\ source_deployment_rel tops am tx
End

(* The fresh EVM frame for this transaction and its entry value transfer. *)
Definition call_entry_rel_def:
  call_entry_rel am tx es <=>
    ?ctxt rb rest.
      es.contexts = (ctxt, rb) :: rest /\
      evm_state_ok es /\ (?d. es.msdomain = Collect d) /\
      frame_fresh ctxt /\ (?mr. ctxt.msgParams.outputTo = Memory mr) /\
      frame_tx_rel tx es ctxt /\ world_rel am tx es /\
      (lookup_account tx.target es.rollback.accounts).code =
        ctxt.msgParams.code
End

Theorem call_ready_deployed:
  call_ready tops runtime_bc am a <=>
    am.logs = [] /\ am.pending_deletions = [] /\
    deployed tops runtime_bc am a
Proof
  simp[call_ready_def, deployed_def]
QED

Triviality accounts_after_transfer_code:
  (lookup_account a (accounts_after_transfer tx accounts)).code =
  (lookup_account a accounts).code
Proof
  rw[accounts_after_transfer_def, lookup_account_def, update_account_def,
     combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> gvs[]
QED

Triviality call_state_rel_entry:
  call_state_rel tops runtime_bc am tx es <=>
    call_entry_rel am tx es /\
    installed_code_rel tops runtime_bc (account_immutables am tx.target)
      (lookup_account tx.target am.accounts).code /\
    source_deployment_rel tops am tx
Proof
  simp[call_state_rel_def, call_entry_rel_def] >>
  eq_tac >> strip_tac >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  `ctxt.msgParams.code = (lookup_account tx.target am.accounts).code` by
    gvs[world_rel_def, accounts_after_transfer_code]
  >- (conj_tac
      >- (qexistsl_tac [`ctxt`, `rb`, `rest`] >> simp[]) >>
      gvs[]) >>
  qexistsl_tac [`ctxt`, `rb`, `rest`] >> gvs[]
QED

Triviality call_source_premises:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx <=>
    call_tx_well_typed tx /\
    !tx'. tx'.target = tx.target /\ call_tx_well_typed tx' ==>
          source_typing_ok tops am tx' /\ source_deployment_rel tops am tx'
Proof
  eq_tac >> strip_tac
  >- (conj_tac >- fs[source_typing_ok_def] >>
      rpt strip_tac >>
      fs[source_typing_ok_def, source_deployment_rel_def, layouts_agree_def] >>
      metis_tac[]) >>
  first_x_assum (qspec_then `tx` mp_tac) >> simp[]
QED

Theorem call_premises_deployed:
  source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es <=>
    deployed tops runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es
Proof
  simp[call_state_rel_entry, deployed_def] >>
  metis_tac[call_source_premises]
QED

(* The constructor result at one filling of the observed gas readings. *)
Definition deploy_result_rel_at_def:
  deploy_result_rel_at gs tops runtime_bc am tx es r es' <=>
    let os = MAP SND (call_trace es) in
    deploy_result_rel
      (storage_trace_horizon
         (deploy_storage_trace (SOME os) gs am tx tops))
      tops runtime_bc tx es r es'
      (load_contract (SOME os) gs am tx [(NONE, tops)] [])
End

Theorem deploy_call_result_rel_from_fillings:
  gas_readings_rel (gas_readings es)
    (\gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs ==>
          deploy_result_rel_at gs tops runtime_bc am tx es r es' /\ P gs) ==>
  deploy_call_result_rel tops runtime_bc am tx es r es'
Proof
  rw[deploy_call_result_rel_def] >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> fs[deploy_result_rel_at_def]
QED

(* TOP-LEVEL: constructor correctness and readiness of a surviving contract. *)
Theorem e2e_deploy_correctness_deployed:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs ==>
               deploy_result_rel_at gs tops runtime_bc am tx es r es' /\
               (~MEM tx.target es'.rollback.toDelete ==>
                !am' rqs.
                  load_contract (SOME (MAP SND (call_trace es))) gs am tx
                    [(NONE, tops)] [] = INL (am', rqs) ==>
                  deployed tops runtime_bc (next_source_machine am' es')
                    tx.target)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all e2eDeployCorrectnessTheory.e2e_deploy_correctness >>
  disch_then (qx_choose_then `r` (qx_choose_then `es'` strip_assume_tac)) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[] >> DISJ2_TAC >>
  `balance_bounded (2 ** 256 - 1) es` by fs[deploy_state_rel_def] >>
  qpat_x_assum `deploy_call_result_rel _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [deploy_call_result_rel_def, LET_THM]) >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  qx_gen_tac `gs` >> BETA_TAC >> strip_tac >> strip_tac >> conj_tac
  >- fs[deploy_result_rel_at_def] >>
  strip_tac >> qx_genl_tac [`am'`, `rqs`] >> strip_tac >>
  `call_ready tops runtime_bc (next_source_machine am' es') tx.target` by
    (irule (INST_TYPE [alpha |-> “:256”] deploy_establishes_call_ready) >>
     rpt (conj_tac >- simp[]) >>
     qexistsl_tac [`storage_trace_horizon (deploy_storage_trace
                      (SOME (MAP SND (call_trace es))) gs am tx tops)`,
                   `am`, `deploy_bc`, `es`, `gs`, `SOME (MAP SND (call_trace es))`,
                   `r`, `rqs`] >>
     gvs[]) >>
  fs[call_ready_deployed]
QED

(* TOP-LEVEL: call correctness in the world supplied by deployment. *)
Theorem vyper_call_correct_deployed:
  !fin policy tops deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deployed tops runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    storage_ok H am tx /\
    call_within H tops am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       calldata_result_rel H tops am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  `source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es` by
    simp[call_premises_deployed] >>
  drule_all e2eCorrectnessTheory.vyper_call_correct >> simp[]
QED

Theorem call_preserves_deployed:
  deployed tops runtime_bc am tx.target /\ call_tx_well_typed tx /\
  runtime_bc <> [] /\ call_entry_rel am tx es /\ LENGTH es.contexts = 1 /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  deployed tops runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  `source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es` by
    simp[call_premises_deployed] >>
  `balance_bounded (2 ** 256 - 1) es` by fs[call_entry_rel_def, evm_state_ok_def] >>
  qpat_x_assum `deployed _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deployed_def]) >>
  drule_all call_frame_preserves_call_ready >> simp[call_ready_deployed]
QED

(* TOP-LEVEL: the sufficient-gas companion for a deployed call. *)
Theorem vyper_call_gas_sufficient_deployed:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deployed tops runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((!f vals.
            calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
              (!gs. call_storage_ok am
                 (tx with <| function_name := f; args := vals |>)
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
              (!obs. ~e2eGasSufficient$gas_source_exempt tops
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>))) /\
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) /\
         frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es` by
    simp[call_premises_deployed] >>
  drule_all e2eGasSufficientTopTheory.vyper_call_gas_sufficient >> simp[]
QED
