(* Single-module compiler headlines with a deployment-to-call handoff. *)
Theory e2eDeployed
Ancestors
  e2eDefs e2eDeployDefs e2eDeployEntry e2eLifecycle e2eComposition
  e2eCorrectness e2eDeployCorrectness[qualified,ignore_grammar]
  e2eGasSufficientTop[qualified,ignore_grammar]
  compileVyper asmOptimizer vyperTypeContractSoundness
  immutableSectionRel vfmState vfmRunCall callTrace frameOutcome frameGas
  vyperInterpreter vyperStorageFootprint stackBoundSoundness stackBoundDefs
  vfmConstants vfmExecutionProp frameRunRaises guardSourceAlignment
  e2eTransactionWorld e2eProducers asmOptNonemptyFinalizer

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

Theorem accounts_after_transfer_code:
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
Theorem e2e_deploy_correctness_deployed_guarded:
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

Triviality deploy_post_storage_ok:
  deploy_typing_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within H tops am tx es /\
  load_contract (SOME (MAP SND (call_trace es))) gs am tx
    [(NONE, tops)] [] = INL (am', rqs) ==>
  storage_ok H am' tx
Proof
  strip_tac >>
  qabbrev_tac `obs = deploy_storage_trace
    (SOME (MAP SND (call_trace es))) gs am tx tops` >>
  `?obs'. load_contract_trace (SOME (MAP SND (call_trace es))) gs am tx
      [(NONE, tops)] [] = (INL (am', rqs), obs')` by
    (qexists_tac `SND (load_contract_trace (SOME (MAP SND (call_trace es)))
      gs am tx [(NONE, tops)] [])` >>
    qpat_x_assum `load_contract _ _ _ _ _ _ = _` mp_tac >>
    simp[load_contract_def] >>
    Cases_on `load_contract_trace (SOME (MAP SND (call_trace es))) gs am tx
      [(NONE, tops)] []` >> gvs[]) >>
  `obs' = obs` by simp[Abbr `obs`, deploy_storage_trace_def] >>
  `load_contract_trace (SOME (MAP SND (call_trace es))) gs am tx
      [(NONE, tops)] [] = (INL (am', rqs), obs)` by
    (qpat_x_assum `load_contract_trace _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `obs' = obs` mp_tac >> simp[]) >>
  `valid_horizon (deploy_evaluation_context tops am tx)
      (initial_state am []) H obs` by
    (simp[valid_horizon_def, storage_trace_horizon_def] >> BETA_TAC >>
    conj_tac >- (irule deploy_empty_storage_well_formed_on >> simp[]) >>
    qpat_x_assum `deploy_within _ _ _ _ _` mp_tac >>
    simp[deploy_within_def, Abbr `obs`]) >>
  `storage_well_formed_on (deploy_evaluation_context tops am tx)
      (initial_state am' []) (FST H)` by
    (simp[deploy_evaluation_context_def] >>
     irule vyperCallFiniteStorageTheory.load_contract_storage_well_formed_on >>
     qpat_x_assum `deploy_typing_ok _ _ _`
       (strip_assume_tac o REWRITE_RULE [deploy_typing_ok_def]) >>
     `?runtime_art. check_contract F am.layouts tx.target
          [(NONE, tops)] = SOME runtime_art` by
       (qpat_x_assum `check_contract T _ _ _ = SOME _` mp_tac >>
        metis_tac[vyperTypeContractModesTheory.check_contract_deploy_implies_runtime]) >>
     conj_tac >- (gvs[call_tx_well_typed_def,
                       vyperTypeInvariantsTheory.context_well_typed_def,
                       initial_evaluation_context_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `runtime_art` >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexists_tac `deploy_art` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`[]`, `gs`, `obs`,
                   `SOME (MAP SND (call_trace es))`, `rqs`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `valid_horizon _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
     simp[valid_horizon_def] >>
     conj_tac >-
       (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
        simp[deploy_evaluation_context_def, initial_evaluation_context_def,
             vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target]) >>
     qpat_x_assum `storage_observations_ok _ _ _` mp_tac >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def,
          vyperCallFiniteStorageSupportTheory.storage_observations_ok_target]) >>
  `storage_well_formed_on
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am' []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     strip_tac >>
     irule (iffRL vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target) >>
     qexists_tac `deploy_evaluation_context tops am tx` >>
     conj_tac >- simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
     first_assum ACCEPT_TAC) >>
  `storage_well_formed_on
      (initial_evaluation_context am'.sources am'.layouts tx NONE)
      (initial_state am' []) (FST H)` by
    (irule (iffRL vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target) >>
     qexists_tac `initial_evaluation_context am.sources am.layouts tx NONE` >>
     conj_tac >- simp[initial_evaluation_context_def] >>
     first_assum ACCEPT_TAC) >>
  simp[storage_ok_def, horizon_ok_def] >> metis_tac[]
QED

(* Transfer the source's storage invariant to the EVM-backed next machine. *)
Theorem deploy_next_storage_ok_from_agreement:
  storage_ok H am' tx /\
  accounts_agree H0 tx.target am'.accounts
    (process_deletions es'.rollback.toDelete
      (update_account tx.target
        (lookup_account tx.target es'.rollback.accounts with
          code := (lookup_account tx.target am'.accounts).code)
        es'.rollback.accounts)) /\
  (!region. MEM region (FST H0) ==> MEM region (FST H)) /\
  ~MEM tx.target es'.rollback.toDelete /\ tx'.target = tx.target ==>
  storage_ok H (next_source_machine am' es') tx'
Proof
  strip_tac >>
  `regions_consistent (FST H)` by fs[storage_ok_def, horizon_ok_def] >>
  `!j b. storage_dead H0 F
       (lookup_account tx.target am'.accounts).storage j b ==>
       storage_dead H F (lookup_account tx.target am'.accounts).storage j b` by
    (rpt strip_tac >>
     qpat_x_assum `storage_dead H0 F _ _ _` mp_tac >>
     simp[loweringStateRelDefsTheory.storage_dead_def] >>
     strip_tac >> qexistsl_tac [`slot`, `tv`] >>
     qpat_x_assum `regions_consistent (FST H)`
       (strip_assume_tac o REWRITE_RULE [regions_consistent_def]) >>
     conj_tac >-
       (qpat_x_assum `!region. MEM region (FST H0) ==> MEM region (FST H)`
          (qspecl_then [`(F,slot,tv)`] mp_tac) >> simp[] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     rpt gen_tac >> strip_tac >> metis_tac[]) >>
  qabbrev_tac `D = storage_dead H0 F
    (lookup_account tx.target am'.accounts).storage` >>
  `storage_agree D (lookup_account tx.target am'.accounts).storage
      (lookup_account tx.target es'.rollback.accounts).storage` by
    (qpat_x_assum `accounts_agree H0 _ _ _`
       (strip_assume_tac o REWRITE_RULE
        [loweringStateRelDefsTheory.accounts_agree_def]) >>
     `((process_deletions es'.rollback.toDelete
          (update_account tx.target
             (lookup_account tx.target es'.rollback.accounts with
              code := (lookup_account tx.target am'.accounts).code)
             es'.rollback.accounts) tx.target).storage =
        (lookup_account tx.target es'.rollback.accounts).storage)` by
       (rw[GSYM lookup_account_def, lookup_account_process_deletions] >>
        rw[lookup_account_def, update_account_def,
           combinTheory.APPLY_UPDATE_THM] >>
        rw[] >> gvs[]) >>
     qpat_x_assum `(process_deletions _ _ _).storage = _`
       (fn h =>
          qpat_x_assum `storage_agree _ _ _`
            (strip_assume_tac o REWRITE_RULE [h])) >>
     rw[Abbr `D`] >>
     metis_tac[lookup_account_def]) >>
  `!j b slot tv. D j b /\ MEM (F,slot,tv) (FST H) /\
      w2n slot <= j /\ j < w2n slot + type_slot_size tv ==>
      dead_bytes (lookup_account tx.target am'.accounts).storage
        (w2n slot) tv j b` by
    (rw[Abbr `D`] >>
     rpt gen_tac >>
     qpat_x_assum `!j b. _` (qspecl_then [`j`, `b`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     drule accountsRelPropsTheory.observed_storage_region_read_live >>
     simp[loweringStateRelDefsTheory.storage_read_live_def] >> metis_tac[]) >>
  qpat_x_assum `storage_ok H am' tx`
    (strip_assume_tac o SIMP_RULE bool_ss [storage_ok_def, horizon_ok_def, LET_THM]) >>
  rw[storage_ok_def, horizon_ok_def] >>
  simp[] >>
  mp_tac (Q.INST
    [`cx` |-> `initial_evaluation_context am'.sources am'.layouts tx NONE`,
     `R1` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`,
     `R2` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`,
     `cx2` |-> `initial_evaluation_context am'.sources am'.layouts tx' NONE`,
     `D` |-> `D`] storage_well_formed_on_horizon_extension) >>
  impl_tac >- gvs[initial_evaluation_context_def] >>
  metis_tac[]
QED

Triviality deploy_next_storage_ok:
  deploy_typing_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within H tops am tx es /\
  deploy_result_rel_at gs tops runtime_bc am tx es r es' /\
  ~MEM tx.target es'.rollback.toDelete /\
  load_contract (SOME (MAP SND (call_trace es))) gs am tx
    [(NONE, tops)] [] = INL (am', rqs) ==>
  !tx'. tx'.target = tx.target ==>
    storage_ok H (next_source_machine am' es') tx'
Proof
  strip_tac >> qx_gen_tac `tx'` >> strip_tac >>
  `storage_ok H am' tx` by
    (irule deploy_post_storage_ok >> metis_tac[]) >>
  qabbrev_tac `H0 = storage_trace_horizon
    (deploy_storage_trace (SOME (MAP SND (call_trace es))) gs am tx tops)` >>
  `accounts_agree H0 tx.target am'.accounts
      (process_deletions es'.rollback.toDelete
        (update_account tx.target
          (lookup_account tx.target es'.rollback.accounts with
             code := (lookup_account tx.target am'.accounts).code)
          es'.rollback.accounts))` by
    (qpat_x_assum `deploy_result_rel_at _ _ _ _ _ _ _ _` mp_tac >>
     simp[deploy_result_rel_at_def, deploy_result_rel_def] >>
     strip_tac >>
     simp[Abbr `H0`] >>
     first_assum ACCEPT_TAC) >>
  `!region. MEM region (FST H0) ==> MEM region (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `deploy_within _ _ _ _ _`
       (strip_assume_tac o BETA_RULE o
        REWRITE_RULE [deploy_within_def, LET_THM]) >>
     qpat_x_assum `!gs. _` (qspecl_then [`gs`] assume_tac) >>
     qpat_x_assum `storage_observations_ok _ _ _`
       (strip_assume_tac o BETA_RULE o
        REWRITE_RULE [storage_observations_ok_def, LET_THM]) >>
     qpat_x_assum `EVERY (\region. MEM region (FST H)) _`
       (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
     qpat_x_assum `!region. _` (qspecl_then [`region`] mp_tac) >>
     simp[storage_trace_regions_def,
          storage_trace_horizon_def, Abbr `H0`] >>
     simp[] >> strip_tac >>
     qpat_x_assum `MEM region _ ==> MEM region (FST H)` irule >>
     gvs[storage_trace_horizon_def, storage_trace_regions_def]) >>
  irule deploy_next_storage_ok_from_agreement >>
  qexistsl_tac [`H0`, `tx`] >> asm_rewrite_tac[]
QED

Triviality deploy_entry_stack_check:
  deploy_state_rel tops deploy_bc am tx es /\
  bytecode_stack_check fuel stack_limit (FST (HD es.contexts)).msgParams.code ==>
  ~frame_raises es StackOverflow
Proof
  rw[deploy_state_rel_def] >>
  rename1 `es.contexts = [(ctxt, rb)]` >>
  qspecl_then [`fuel`, `stack_limit`, `ctxt.msgParams.code`, `es`]
    mp_tac bytecode_stack_check_no_overflow >>
  gvs[]
QED

Definition frame_starved_def:
  frame_starved es r es' <=>
    ?exc out lgs.
      (exc = OutOfGas \/
       exc = StackOverflow /\
       ~(?fuel. bytecode_stack_check fuel stack_limit
                  (FST (HD es.contexts)).msgParams.code)) /\
      frame_outcome es r es' (SOME exc) out lgs /\ frame_raises es exc
End

(* TOP-LEVEL: constructor correctness over a fixed storage horizon. *)
Theorem e2e_deploy_correctness_deployed:
  !fin policy tops deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok tops am tx /\
    deploy_entry_rel tops deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    horizon_ok H /\
    deploy_within H tops am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gs. deploy_result_rel_at gs tops runtime_bc am tx es r es' /\
               (~MEM tx.target es'.rollback.toDelete ==>
                !am' rqs.
                  load_contract (SOME (MAP SND (call_trace es))) gs am tx
                    [(NONE, tops)] [] = INL (am', rqs) ==>
                  deployed tops runtime_bc (next_source_machine am' es')
                    tx.target /\
                  (!tx'. tx'.target = tx.target ==>
                    storage_ok H (next_source_machine am' es') tx'))))
Proof
  rpt gen_tac >> strip_tac >>
  `deploy_state_rel tops deploy_bc am tx es /\
   (lookup_account tx.target am.accounts).storage = empty_storage /\
   am.tStorage tx.target = empty_storage` by
    metis_tac[deploy_entry_rel_state] >>
  `!gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs` by
    (irule deploy_storage_ok_from_within >> metis_tac[]) >>
  drule_all e2e_deploy_correctness_deployed_guarded >>
  disch_then (qx_choose_then `r` (qx_choose_then `es'` strip_assume_tac)) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[]
  >- (DISJ1_TAC >>
      qpat_x_assum `creation_resource_starved _ _ _`
        (strip_assume_tac o REWRITE_RULE [creation_resource_starved_def]) >>
      `wf_state es /\ LENGTH es.contexts = 1` by fs[deploy_state_rel_def] >>
      `~vfmExecution$vfm_abort (SOME exc)` by
        (Cases_on `exc` >> gvs[vfmExecutionTheory.vfm_abort_def]) >>
      `frame_raises es exc` by (drule_all run_call_root_frame_outcome_raises >> simp[]) >>
      PURE_REWRITE_TAC [frame_starved_def] >>
      qexistsl_tac [`exc`, `out`, `lgs`] >>
      (conj_tac >- metis_tac[deploy_entry_stack_check] >> asm_rewrite_tac[])) >>
  DISJ2_TAC >>
  drule gas_readings_rel_mono >>
  disch_then irule >>
  qx_gen_tac `gs` >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!gs. deploy_storage_ok _ _ _ _ gs`
    (qspecl_then [`gs`] assume_tac) >>
  conj_tac >- simp[] >>
  strip_tac >> qx_genl_tac [`am'`, `rqs`] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  match_mp_tac deploy_next_storage_ok >> fs[horizon_ok_def] >> metis_tac[]
QED

Theorem call_entry_stack_check:
  call_entry_rel am tx es /\
  bytecode_stack_check fuel stack_limit (FST (HD es.contexts)).msgParams.code ==>
  ~frame_raises es StackOverflow
Proof
  rw[call_entry_rel_def, evm_state_ok_def, frame_fresh_def] >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  `bytecode_stack_check fuel stack_limit ctxt.msgParams.code` by
    (qpat_x_assum `bytecode_stack_check _ _ _` mp_tac >> simp[]) >>
  qspecl_then [`fuel`, `stack_limit`, `ctxt.msgParams.code`, `es`]
    mp_tac bytecode_stack_check_no_overflow >>
  simp[]
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

(* TOP-LEVEL: call correctness and preservation of a surviving deployment. *)
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
      (frame_starved es r es' \/
       calldata_result_rel H tops am tx es r es') /\
      (LENGTH es.contexts = 1 /\ ~MEM tx.target es'.rollback.toDelete ==>
       deployed tops runtime_bc (transaction_world am r es') tx.target)
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bc <> []` by
    (fs[accepted_finalizers_def]
     >- (gvs[] >> metis_tac[compile_vyper_runtime_nonempty]) >>
     gvs[] >> drule compile_vyper_runtime_phases_asm_opt >>
     metis_tac[codegen_assembly_finalizer_nonempty]) >>
  `source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es` by
    simp[call_premises_deployed] >>
  drule_all e2eCorrectnessTheory.vyper_call_correct >>
  disch_then (qx_choosel_then [`r`, `es'`]
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexistsl_tac [`r`, `es'`] >> asm_rewrite_tac[] >>
  reverse conj_tac
  >- (strip_tac >> Cases_on `r = INR NONE` >> simp[transaction_world_def] >>
      Cases_on `call_external NONE [] am tx` >>
      rename1 `call_external NONE [] am tx = (res, output)` >>
      PairCases_on `output` >>
      rename1 `call_external NONE [] am tx = (res, am_out, rqs)` >>
      `next_source_machine am_out es' = next_source_machine am es'` by
        (irule call_external_next_source_machine >>
         fs[call_state_rel_def] >> metis_tac[]) >>
      drule_all call_preserves_deployed >> simp[]) >>
  qpat_x_assum `frame_resource_starved _ _ _ \/ _` strip_assume_tac >>
  asm_rewrite_tac[] >>
  DISJ1_TAC >>
  qpat_x_assum `frame_resource_starved _ _ _`
    (strip_assume_tac o REWRITE_RULE [frame_resource_starved_def]) >>
  PURE_REWRITE_TAC [frame_starved_def] >>
  qexistsl_tac [`exc`, `out`, `lgs`] >>
  (conj_tac >- metis_tac[call_entry_stack_check] >> asm_rewrite_tac[])
QED

(* The per-filling form of the deployed call gas companion. *)
Theorem vyper_call_gas_sufficient_deployed_guarded:
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
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) ==>
         ~frame_raises (add_frame_gas g' es) OutOfGas)
Proof
  rpt gen_tac >> strip_tac >>
  `source_typing_ok tops am tx /\ call_state_rel tops runtime_bc am tx es` by
    simp[call_premises_deployed] >>
  drule_all e2eGasSufficientTopTheory.vyper_call_gas_sufficient >> simp[]
QED

(* TOP-LEVEL: the sufficient-gas companion for a deployed call. *)
Theorem vyper_call_gas_sufficient_deployed:
  !fin policy tops deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deployed tops runtime_bc am tx.target /\
    call_tx_well_typed tx /\ call_entry_rel am tx es /\
    storage_ok H am tx
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (call_within H tops am tx (add_frame_gas g' es) /\
         (!f vals.
            calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
              (!obs. ~e2eGasSufficient$gas_source_exempt tops
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>))) /\
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) ==>
         ~frame_raises (add_frame_gas g' es) OutOfGas)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all vyper_call_gas_sufficient_deployed_guarded >>
  disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> strip_tac >>
  first_x_assum irule >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!f vals. calldata_dispatch _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> gen_tac >>
  irule valid_horizon_call_storage_ok >>
  qexists_tac `H` >> metis_tac[valid_horizon_for_dispatch]
QED
