(* Linked compiler headlines with a deployment-to-call handoff. *)
Theory e2eModsDeployed
Ancestors
  e2eDeployed e2eModsLifecycle e2eModsDefs e2eDeployModsDefs
  e2eModsTopsDraft[qualified,ignore_grammar]
  e2eDefs e2eGasSufficient e2eCorrectness e2eComposition linkedCallStorage compileUnit
  asmOptimizer vyperInterpreter vyperContext vyperStorageFootprint
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeInvariants
  vyperTypeContractModes[qualified] vyperCallFiniteStorage
  vyperCallFiniteStorageSupport vyperStorageBackend vfmState vfmRunCall vfmExecutionProp
  vfmConstants frameOutcome frameGas frameRunRaises stackBoundDefs
  stackBoundSoundness callTrace guardSourceAlignment
  e2eTransactionWorld linkedCompilePhases codegenAsmProgOk asmOptNonemptyFinalizer

(* Readiness of the installed unit, independent of transaction bookkeeping. *)
Definition deployed_mods_def:
  deployed_mods mods exps runtime_bc am a <=>
    call_ready_mods mods exps runtime_bc
      (am with <| logs := []; pending_deletions := [] |>) a
End

Triviality deployed_mods_facts:
  deployed_mods mods exps runtime_bc am a <=>
    installed_code_rel_mods mods runtime_bc (account_immutables am a)
      (lookup_account a am.accounts).code /\
    !tx. tx.target = a /\ call_tx_well_typed tx ==>
         source_typing_ok_mods mods exps am tx /\
         source_deployment_rel_mods mods exps am tx
Proof
  simp[deployed_mods_def, call_ready_mods_def, account_immutables_def,
       source_typing_ok_mods_def, source_deployment_rel_mods_def,
       machine_well_typed_def, layouts_agree_mods_def]
QED

Theorem deployed_mods_singleton:
  deployed_mods [(NONE, tops)] [] = deployed tops
Proof
  simp[FUN_EQ_THM, deployed_mods_facts, deployed_def,
       installed_code_rel_mods_singleton, source_typing_ok_mods_singleton,
       source_deployment_rel_mods_singleton]
QED

Theorem call_ready_deployed_mods:
  call_ready_mods mods exps runtime_bc am a <=>
    am.logs = [] /\ am.pending_deletions = [] /\
    deployed_mods mods exps runtime_bc am a
Proof
  simp[call_ready_mods_def, deployed_mods_facts]
QED

Triviality call_state_rel_entry_mods:
  call_state_rel_mods mods exps runtime_bc am tx es <=>
    call_entry_rel am tx es /\
    installed_code_rel_mods mods runtime_bc (account_immutables am tx.target)
      (lookup_account tx.target am.accounts).code /\
    source_deployment_rel_mods mods exps am tx
Proof
  simp[call_state_rel_mods_def, call_entry_rel_def] >>
  eq_tac >> strip_tac >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  `ctxt.msgParams.code = (lookup_account tx.target am.accounts).code` by
    gvs[world_rel_def, accounts_after_transfer_code]
  >- (conj_tac
      >- (qexistsl_tac [`ctxt`, `rb`, `rest`] >> simp[]) >>
      gvs[]) >>
  qexistsl_tac [`ctxt`, `rb`, `rest`] >> gvs[]
QED

Triviality call_source_premises_mods:
  source_typing_ok_mods mods exps am tx /\
  source_deployment_rel_mods mods exps am tx <=>
    call_tx_well_typed tx /\
    !tx'. tx'.target = tx.target /\ call_tx_well_typed tx' ==>
          source_typing_ok_mods mods exps am tx' /\
          source_deployment_rel_mods mods exps am tx'
Proof
  eq_tac >> strip_tac
  >- (conj_tac >- fs[source_typing_ok_mods_def] >>
      rpt strip_tac >>
      fs[source_typing_ok_mods_def, source_deployment_rel_mods_def,
         layouts_agree_mods_def] >>
      metis_tac[]) >>
  first_x_assum (qspec_then `tx` mp_tac) >> simp[]
QED

Theorem call_premises_deployed_mods:
  source_typing_ok_mods mods exps am tx /\
  call_state_rel_mods mods exps runtime_bc am tx es <=>
    deployed_mods mods exps runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es
Proof
  simp[call_state_rel_entry_mods, deployed_mods_facts] >>
  metis_tac[call_source_premises_mods]
QED

Triviality compile_vyper_mods_runtime_nonempty:
  fin IN accepted_finalizers /\
  compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) ==>
  runtime_bc <> []
Proof
  strip_tac >>
  qpat_assum `compile_vyper_mods _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP compile_vyper_with_mods_success_phases o
     REWRITE_RULE [compile_vyper_mods_def]) >>
  qpat_assum `finalize_codegen fin rpolicy runtime_out.po_unit = SOME runtime_bc`
    (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
  Cases_on `fin = K SOME`
  >- (drule codegen_assembly_nonempty >> gvs[]) >>
  `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  qpat_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
  qpat_x_assum `runtime_bc = assemble prog'` SUBST1_TAC >>
  irule codegen_assembly_finalizer_nonempty >>
  qexistsl [`prog`, `rpolicy`, `runtime_out.po_unit`] >> simp[]
QED

Theorem call_preserves_deployed_mods:
  deployed_mods mods exps runtime_bc am tx.target /\ call_tx_well_typed tx /\
  runtime_bc <> [] /\ call_entry_rel am tx es /\ LENGTH es.contexts = 1 /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  deployed_mods mods exps runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  `source_typing_ok_mods mods exps am tx /\
   call_state_rel_mods mods exps runtime_bc am tx es` by
    simp[call_premises_deployed_mods] >>
  `balance_bounded (2 ** 256 - 1) es` by fs[call_entry_rel_def, evm_state_ok_def] >>
  qpat_x_assum `deployed_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deployed_mods_facts]) >>
  drule_all call_frame_preserves_call_ready_mods >> simp[call_ready_deployed_mods]
QED

(* TOP-LEVEL: linked call correctness and preservation of a surviving deployment. *)
Theorem vyper_call_correct_deployed_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    deployed_mods mods exps runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    storage_ok H am tx /\
    call_within_mods H mods exps am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_starved es r es' \/
       calldata_result_rel_mods H mods exps am tx es r es') /\
      (LENGTH es.contexts = 1 /\ ~MEM tx.target es'.rollback.toDelete ==>
       deployed_mods mods exps runtime_bc (transaction_world am r es') tx.target)
Proof
  rpt gen_tac >> strip_tac >>
  `source_typing_ok_mods mods exps am tx /\
   call_state_rel_mods mods exps runtime_bc am tx es` by
    simp[call_premises_deployed_mods] >>
  drule_all e2eModsTopsDraftTheory.vyper_call_correct_mods >>
  disch_then (qx_choosel_then [`r`, `es'`]
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[] >>
  reverse conj_tac
  >- (strip_tac >> Cases_on `r = INR NONE` >> simp[transaction_world_def] >>
      `runtime_bc <> []` by (drule_all compile_vyper_mods_runtime_nonempty >> simp[]) >>
      `source_deployment_rel_mods mods exps am tx` by fs[call_state_rel_entry_mods] >>
      Cases_on `call_external NONE [] am tx` >>
      rename1 `call_external NONE [] am tx = (res, output)` >>
      PairCases_on `output` >>
      rename1 `call_external NONE [] am tx = (res, am_out, rqs)` >>
      `next_source_machine am_out es' = next_source_machine am es'` by
        (irule call_external_next_source_machine_mods >> metis_tac[]) >>
      drule_all call_preserves_deployed_mods >> simp[]) >>
  qpat_x_assum `frame_resource_starved _ _ _ \/ _` strip_assume_tac >>
  asm_rewrite_tac[] >>
  DISJ1_TAC >>
  qpat_x_assum `frame_resource_starved _ _ _`
    (strip_assume_tac o REWRITE_RULE [frame_resource_starved_def]) >>
  PURE_REWRITE_TAC [frame_starved_def] >>
  qexistsl_tac [`exc`, `out`, `lgs`] >>
  (conj_tac >- metis_tac[call_entry_stack_check] >> asm_rewrite_tac[])
QED

(* TOP-LEVEL: sufficient gas for a deployed linked call. *)
Theorem vyper_call_gas_sufficient_deployed_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    deployed_mods mods exps runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es /\
    storage_ok H am tx
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_within_mods H mods exps am tx (add_frame_gas g' es) /\
         (!f vals.
            calldata_dispatch_mods mods exps tx.calldata = SOME (f, vals) ==>
              (!obs. ~gas_source_exempt_mods mods
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>))) /\
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) ==>
         ~frame_raises (add_frame_gas g' es) OutOfGas)
Proof
  rpt gen_tac >> strip_tac >>
  `source_typing_ok_mods mods exps am tx /\
   call_state_rel_mods mods exps runtime_bc am tx es` by
    simp[call_premises_deployed_mods] >>
  drule_all e2eModsTopsDraftTheory.vyper_call_gas_sufficient_mods >>
  disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> strip_tac >>
  first_x_assum irule >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!f vals. calldata_dispatch_mods _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> gen_tac >>
  irule valid_horizon_call_storage_ok >>
  qexists_tac `H` >> metis_tac[valid_horizon_for_dispatch_mods]
QED

Triviality deploy_post_storage_ok_mods:
  deploy_typing_ok_mods mods exps am tx /\ horizon_ok H /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within_mods H mods exps am tx es /\
  load_contract (SOME (MAP SND (call_trace es))) gs am tx mods exps =
    INL (am', rqs) ==>
  storage_ok H am' tx
Proof
  strip_tac >>
  qabbrev_tac `orc = SOME (MAP SND (call_trace es))` >>
  qabbrev_tac `obs = deploy_storage_trace_mods orc gs am tx mods exps` >>
  `load_contract_trace orc gs am tx mods exps = (INL (am', rqs), obs)` by
    (Cases_on `load_contract_trace orc gs am tx mods exps` >>
     gvs[Abbr `obs`, deploy_storage_trace_mods_def, load_contract_def]) >>
  `valid_horizon (deploy_evaluation_context_mods mods am tx)
      (initial_state am []) H obs` by
    (fs[valid_horizon_def, horizon_ok_def] >>
     conj_tac
     >- (irule empty_storage_well_formed_on >>
         Cases >> gvs[get_storage_def, deploy_evaluation_context_mods_def,
                      initial_evaluation_context_def, initial_state_def,
                      lookup_account_def]) >>
     qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
     simp[deploy_within_mods_def, Abbr `obs`, Abbr `orc`]) >>
  qpat_x_assum `deploy_typing_ok_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_typing_ok_mods_def]) >>
  `?runtime_art. check_contract F am.layouts tx.target mods = SOME runtime_art` by
    metis_tac[vyperTypeContractModesTheory.check_contract_deploy_implies_runtime] >>
  `storage_well_formed_on (deploy_evaluation_context_mods mods am tx)
      (initial_state am' []) (FST H)` by
    (simp[deploy_evaluation_context_mods_def] >>
     irule load_contract_storage_well_formed_on >>
     conj_tac >- fs[call_tx_well_typed_def, context_well_typed_def,
                     initial_evaluation_context_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `runtime_art` >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `deploy_art` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`exps`, `gs`, `obs`, `orc`, `rqs`] >>
     simp[GSYM deploy_evaluation_context_mods_def]) >>
  simp[storage_ok_def] >>
  irule (iffRL storage_well_formed_on_target) >>
  qexists_tac `deploy_evaluation_context_mods mods am tx` >>
  simp[deploy_evaluation_context_mods_def, initial_evaluation_context_def]
QED

Triviality deploy_next_storage_ok_mods:
  deploy_typing_ok_mods mods exps am tx /\ horizon_ok H /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within_mods H mods exps am tx es /\
  deploy_result_rel_mods
    (storage_trace_horizon (deploy_storage_trace_mods
      (SOME (MAP SND (call_trace es))) gs am tx mods exps))
    mods runtime_bc tx es r es' (INL (am', rqs)) /\
  ~MEM tx.target es'.rollback.toDelete /\
  load_contract (SOME (MAP SND (call_trace es))) gs am tx mods exps =
    INL (am', rqs) ==>
  !tx'. tx'.target = tx.target ==>
    storage_ok H (next_source_machine am' es') tx'
Proof
  strip_tac >> qx_gen_tac `tx'` >> strip_tac >>
  `storage_ok H am' tx` by (irule deploy_post_storage_ok_mods >> metis_tac[]) >>
  qabbrev_tac `obs =
    deploy_storage_trace_mods (SOME (MAP SND (call_trace es))) gs am tx mods exps` >>
  `storage_observations_ok (deploy_evaluation_context_mods mods am tx) H obs` by
    (qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
     simp[deploy_within_mods_def, Abbr `obs`]) >>
  irule deploy_next_storage_ok_from_agreement >>
  qexistsl_tac [`storage_trace_horizon obs`, `tx`] >>
  simp[] >> conj_tac
  >- fs[storage_observations_ok_def, storage_trace_horizon_def, listTheory.EVERY_MEM] >>
  qpat_x_assum `deploy_result_rel_mods _ _ _ _ _ _ _ _` mp_tac >>
  simp[deploy_result_rel_mods_def, Abbr `obs`] >> metis_tac[]
QED

Triviality deploy_frame_starved_mods:
  deploy_entry_rel_mods mods exps deploy_bc am tx es /\
  run_call es = SOME (r, es') /\ creation_resource_starved es r es' ==>
  frame_starved es r es'
Proof
  strip_tac >>
  qpat_x_assum `creation_resource_starved _ _ _`
    (strip_assume_tac o REWRITE_RULE [creation_resource_starved_def]) >>
  `wf_state es /\ LENGTH es.contexts = 1` by
    fs[deploy_entry_rel_mods_def, evm_state_ok_def] >>
  `~vfmExecution$vfm_abort (SOME exc)` by
    (Cases_on `exc` >> gvs[vfmExecutionTheory.vfm_abort_def]) >>
  `frame_raises es exc` by (drule_all run_call_root_frame_outcome_raises >> simp[]) >>
  `!fuel. bytecode_stack_check fuel stack_limit
           (FST (HD es.contexts)).msgParams.code ==>
         ~frame_raises es StackOverflow` by
    (gen_tac >> strip_tac >>
     qspecl_then [`fuel`, `stack_limit`,
                  `(FST (HD es.contexts)).msgParams.code`, `es`]
       mp_tac bytecode_stack_check_no_overflow >>
     gvs[deploy_entry_rel_mods_def, frame_fresh_def]) >>
  PURE_REWRITE_TAC [frame_starved_def] >>
  qexistsl_tac [`exc`, `out`, `lgs`] >>
  (conj_tac >- metis_tac[] >> asm_rewrite_tac[])
QED

(* TOP-LEVEL: linked constructor correctness and readiness over a fixed horizon. *)
Theorem e2e_deploy_correctness_deployed_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok_mods mods exps am tx /\
    deploy_entry_rel_mods mods exps deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    horizon_ok H /\
    deploy_within_mods H mods exps am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gs. deploy_result_rel_mods
                 (storage_trace_horizon (deploy_storage_trace_mods
                   (SOME (MAP SND (call_trace es))) gs am tx mods exps))
                 mods runtime_bc tx es r es'
                 (load_contract (SOME (MAP SND (call_trace es))) gs am tx mods exps) /\
               (~MEM tx.target es'.rollback.toDelete ==>
                !am' rqs.
                  load_contract (SOME (MAP SND (call_trace es))) gs am tx
                    mods exps = INL (am', rqs) ==>
                  deployed_mods mods exps runtime_bc (next_source_machine am' es')
                    tx.target /\
                  (!tx'. tx'.target = tx.target ==>
                    storage_ok H (next_source_machine am' es') tx'))))
Proof
  rpt gen_tac >> strip_tac >>
  `deploy_state_rel_mods mods exps deploy_bc am tx es /\
   (lookup_account tx.target am.accounts).storage = empty_storage /\
   am.tStorage tx.target = empty_storage` by
    (irule e2eModsTopsDraftTheory.deploy_entry_rel_state_mods >>
     fs[deploy_typing_ok_mods_def] >> metis_tac[]) >>
  `!gs. deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace es)) gs` by
    (irule e2eModsTopsDraftTheory.deploy_storage_ok_from_within_mods >> metis_tac[]) >>
  `balance_bounded (2 ** 256 - 1) es` by fs[deploy_state_rel_mods_def] >>
  drule_all e2eModsTopsDraftTheory.e2e_deploy_correctness_mods >>
  disch_then (qx_choosel_then [`r`, `es'`] strip_assume_tac) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[]
  >- metis_tac[deploy_frame_starved_mods] >>
  DISJ2_TAC >>
  qpat_x_assum `deploy_call_result_rel_mods _ _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [deploy_call_result_rel_mods_def, LET_THM]) >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  qx_gen_tac `gs` >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!gs. deploy_storage_ok_mods _ _ _ _ _ gs`
    (qspec_then `gs` assume_tac) >>
  conj_tac >- simp[] >>
  strip_tac >> qx_genl_tac [`am'`, `rqs`] >> strip_tac >>
  conj_tac
  >- (`call_ready_mods mods exps runtime_bc (next_source_machine am' es')
        tx.target` by
        (irule (INST_TYPE [alpha |-> “:256”] deploy_establishes_call_ready_mods) >>
         rpt (conj_tac >- simp[]) >>
         qexistsl_tac [`storage_trace_horizon (deploy_storage_trace_mods
                          (SOME (MAP SND (call_trace es))) gs am tx mods exps)`,
                       `am`, `deploy_bc`, `es`, `gs`, `SOME (MAP SND (call_trace es))`,
                       `r`, `rqs`] >>
         gvs[]) >>
      fs[call_ready_deployed_mods]) >>
  match_mp_tac deploy_next_storage_ok_mods >> metis_tac[]
QED

local
  fun singleton_equivalence linked original =
    let
      val (linked_vars, linked_body) = strip_forall (concl linked)
      val (original_vars as fin :: policy :: tops :: rest, _) =
        strip_forall (concl original)
      val instance = subst
        (ListPair.mapEq (op |->)
          (linked_vars, fin :: policy :: ``[(NONE:num option, ^tops)]`` ::
            ``[]:(string # num) list`` :: rest))
        linked_body
    in
      mk_eq (list_mk_forall (original_vars, instance), concl original)
    end
in

Theorem e2e_deploy_correctness_deployed_mods_singleton:
  ^(singleton_equivalence e2e_deploy_correctness_deployed_mods
      e2e_deploy_correctness_deployed)
Proof
  simp[compile_vyper_mods_singleton, deploy_typing_ok_mods_singleton,
       deploy_entry_rel_mods_singleton, deploy_within_mods_singleton,
       deploy_result_rel_mods_singleton, deploy_storage_trace_mods_singleton,
       deploy_result_rel_at_def, deployed_mods_singleton, LET_THM]
QED

Theorem vyper_call_correct_deployed_mods_singleton:
  ^(singleton_equivalence vyper_call_correct_deployed_mods
      vyper_call_correct_deployed)
Proof
  simp[compile_vyper_mods_singleton, deployed_mods_singleton,
       call_within_mods_singleton, calldata_result_rel_mods_singleton]
QED

Theorem vyper_call_gas_sufficient_deployed_mods_singleton:
  ^(singleton_equivalence vyper_call_gas_sufficient_deployed_mods
      vyper_call_gas_sufficient_deployed)
Proof
  simp[compile_vyper_mods_singleton, deployed_mods_singleton,
       call_within_mods_singleton, calldata_dispatch_mods_singleton,
       gas_source_exempt_mods_singleton]
QED

end
