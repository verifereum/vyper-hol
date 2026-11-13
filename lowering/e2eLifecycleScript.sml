(*
 * Milestone 7 lifecycle producers: the environmental premises of
 * vyper_call_correct that depend only on the source machine and the
 * contract's address hold after a deployment and again after every call,
 * on the machine the next transaction starts from (next_source_machine).
 *
 * call_ready: those premises, for every later transaction to the address.
 * deploy_establishes_call_ready / deploy_call_result_establishes_call_ready:
 *   deployment to call handoff.
 * call_preserves_call_ready: call to call handoff, for every call result.
 * deploy_empty_storage_well_formed_on: zero storage decodes on every region.
 *)
Theory e2eLifecycle
Ancestors
  e2eDefs e2eDeployDefs ctorDeployDeadLoad supportedProgram
  vyperInterpreter vyperTypeContract vyperTypeContractSoundness
  vyperTypeDeploymentMachine vyperTypeExternalCallMachine
  vyperTypeInitialState vyperTypeInvariants
  vyperStorageFootprint vyperStorageBackend vyperLookupStorage vyperStorage
  immutableSectionRel vyperABIEntries
  vfmState vfmExecution vfmExecutionProp vfmRunCall vfmTotalBalance
  vfmAccountFrame vfmContext loweringStateRelDefs While
  e2eCodeFrame vyperRuntimeImmutables storageLiveAgree vyperCallFiniteStorage

(* ===== The premises a later call needs from the machine ===== *)

(* Every premise of vyper_call_correct that depends only on the source
   machine am and the contract's address a, for any later transaction to a:
   the machine's own transaction-boundary fields, the installed code, and the
   source typing and deployment relations. The EVM-entry conjuncts of
   call_state_rel (the fresh frame, the value transfer) belong to the
   environment that starts the transaction. *)
Definition call_ready_def:
  call_ready tops runtime_bc am a <=>
    am.logs = [] /\ am.pending_deletions = [] /\
    installed_code_rel tops runtime_bc (account_immutables am a)
      (lookup_account a am.accounts).code /\
    !tx. tx.target = a /\ call_tx_well_typed tx ==>
         source_typing_ok tops am tx /\ source_deployment_rel tops am tx
End

(* ===== EVM facts ===== *)

Theorem lookup_account_process_deletions:
  !ds accs a.
    lookup_account a (process_deletions ds accs) =
    if MEM a ds then empty_account_state else lookup_account a accs
Proof
  simp[lookup_account_def] >> Induct >>
  gvs[process_deletions_def, update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> gvs[]
QED

Theorem run_call_balance_bounded:
  wf_state es /\ balance_bounded B es /\ run_call es = SOME (r, es') ==>
  balance_bounded B es'
Proof
  rpt strip_tac >> gvs[run_call_def] >>
  `(\p. wf_state (SND p) /\ balance_bounded B (SND p)) (r, es')`
    suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  goal_assum $ drule_at Any >> simp[] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> strip_tac >>
  simp[step_preserves_wf_state] >>
  drule step_total_balance_bounded >> gvs[balance_bounded_def]
QED

(* After a run from a well-formed state whose balances total below 2^256,
   every account is well typed: balance from the total, code length from
   wf_state (EIP-170). *)
Theorem run_call_accounts_well_typed:
  wf_state es /\ balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') ==>
  accounts_well_typed es'.rollback.accounts
Proof
  strip_tac >>
  drule_all run_call_balance_bounded >> strip_tac >>
  drule_all run_call_preserves_wf_state >> strip_tac >>
  rw[accounts_well_typed_def, account_well_typed_def]
  >- (drule balance_bounded_rollback >> strip_tac >>
      irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
      irule_at Any lookup_balance_le_total_balance >>
      fs[] >> decide_tac) >>
  gvs[wf_state_def, all_accounts_def, wf_accounts_def, wf_account_state_def,
      lookup_account_def]
QED

(* ===== Source facts ===== *)

Theorem call_external_function_trace_runtime_static_fields[local]:
  ~cx.in_deploy /\
  call_external_function_trace orc gobs am cx nr mut ts all_mods args dflts
    vals fbody ret = (outcome, am_out, rqs, obs) ==>
  am_out.sources = am.sources /\ am_out.exports = am.exports /\
  am_out.layouts = am.layouts
Proof
  simp_tac bool_ss [call_external_function_trace_def, LET_THM] >>
  IF_CASES_TAC >- simp[] >>
  strip_tac >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs(), abstract_machine_from_state_def]
QED

(* A call leaves the machine's source fields alone. *)
Theorem call_external_static_fields:
  call_external orc gobs am tx = (res, am', rqs) ==>
  am'.sources = am.sources /\ am'.exports = am.exports /\
  am'.layouts = am.layouts
Proof
  simp_tac bool_ss [call_external_def] >>
  Cases_on `call_external_trace orc gobs am tx` >>
  rename1 `call_external_trace orc gobs am tx = (trace_res, trace_rest)` >>
  PairCases_on `trace_rest` >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `call_external_trace _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_trace_def, LET_THM] >>
  Cases_on `ALOOKUP am.sources tx.target` >> simp[] >>
  qmatch_goalsub_abbrev_tac `option_CASE code_opt` >>
  Cases_on `code_opt` >> simp[] >>
  qmatch_goalsub_abbrev_tac `lookup_exported_function cx am tx.function_name` >>
  Cases_on `lookup_exported_function cx am tx.function_name` >> simp[] >>
  rename1 `SOME func` >> PairCases_on `func` >> simp[] >>
  qmatch_goalsub_rename_tac `call_external_function_trace orc gobs am cx nr mut ts mods argtys defaults vals stmts retty` >>
  Cases_on `call_external_function_trace orc gobs am cx nr mut ts mods argtys defaults vals stmts retty` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (outcome, output_rest)` >>
  PairCases_on `output_rest` >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  drule_all call_external_function_trace_runtime_static_fields >>
  strip_tac >>
  namedCases_on `outcome` ["value", "exc"] >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `exc` >> simp[] >> strip_tac >> gvs[]
QED

(* ===== The machine after a transaction ===== *)

Theorem next_source_machine_fields[simp]:
  (next_source_machine am' es').sources = am'.sources /\
  (next_source_machine am' es').exports = am'.exports /\
  (next_source_machine am' es').layouts = am'.layouts /\
  (next_source_machine am' es').immutables = am'.immutables /\
  (next_source_machine am' es').logs = [] /\
  (next_source_machine am' es').pending_deletions = [] /\
  (next_source_machine am' es').accounts =
    process_deletions es'.rollback.toDelete es'.rollback.accounts /\
  (next_source_machine am' es').tStorage = empty_transient_storage
Proof
  simp[next_source_machine_def]
QED

Theorem next_source_machine_well_typed:
  EVERY (\(addr, imms). imms_well_typed imms) am'.immutables /\
  accounts_well_typed es'.rollback.accounts ==>
  machine_well_typed (next_source_machine am' es')
Proof
  simp[machine_well_typed_def, accounts_well_typed_process_deletions]
QED

Theorem account_immutables_next_source_machine[simp]:
  account_immutables (next_source_machine am' es') a = account_immutables am' a
Proof
  simp[account_immutables_def]
QED

Theorem layouts_agree_cong[local]:
  ALOOKUP am2.layouts tx2.target = ALOOKUP am1.layouts tx1.target ==>
  (layouts_agree tops am2 tx2 <=> layouts_agree tops am1 tx1)
Proof
  simp[layouts_agree_def]
QED

(* A checked single-module contract deploys with valid empty exports. *)
Theorem check_contract_exports_ok_empty[local]:
  check_contract b layouts addr [(NONE, tops)] = SOME art ==>
  exports_ok layouts2 addr2 [(NONE, tops)] []
Proof
  strip_tac >> drule check_contract_external_method_ids_distinct >>
  disch_then (qspecl_then [`tops`, `NONE`] mp_tac) >>
  simp[exports_ok_def, abi_deployed_signatures_def,
       abi_external_method_ids_def]
QED

(* ===== Deployment to call ===== *)

Theorem deploy_establishes_call_ready:
  deploy_typing_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  supported_program tops /\ supported_program_deploy tops /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  load_contract orc gs am tx [(NONE, tops)] [] = INL (am', rqs) /\
  deploy_result_rel H tops runtime_bc tx es r es' (INL (am', rqs)) ==>
  call_ready tops runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  gvs[deploy_typing_ok_constants_ready] >>
  `wf_state es /\ layouts_agree tops am tx` by fs[deploy_state_rel_def] >>
  drule_all load_contract_sources_layouts >> strip_tac >>
  `context_well_typed
     (initial_evaluation_context ((tx.target, [(NONE, tops)]) :: am.sources)
        am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    gvs[context_well_typed_def, initial_evaluation_context_def,
        call_tx_well_typed_def] >>
  `machine_well_typed am'` by
    (irule load_contract_establishes_machine_well_typed >>
     goal_assum $ drule_at Any >> simp[] >>
     goal_assum $ drule_at Any >> simp[]) >>
  `accounts_well_typed es'.rollback.accounts` by
    (irule run_call_accounts_well_typed >>
     goal_assum $ drule_at Any >> simp[]) >>
  `ALOOKUP am'.exports tx.target = SOME []` by
    metis_tac[load_contract_deployed_exports] >>
  simp[call_ready_def] >> conj_tac
  >- (gvs[deploy_result_rel_def, installed_code_rel_def,
          lookup_account_process_deletions] >>
      metis_tac[]) >>
  qx_gen_tac `tx2` >> strip_tac >>
  `checked_contract_runtime_ready runtime_art [(NONE, tops)] am' tx2` by
    (irule load_contract_establishes_checked_contract_runtime_ready >>
     qpat_assum `load_contract _ _ _ _ _ _ = _` (irule_at Any) >>
     gvs[listTheory.CONS_ACYCLIC] >>
     metis_tac[check_contract_exports_ok_empty]) >>
  `machine_well_typed (next_source_machine am' es')` by
    (irule next_source_machine_well_typed >> fs[machine_well_typed_def]) >>
  `layouts_agree tops (next_source_machine am' es') tx2` by
    metis_tac[layouts_agree_cong, next_source_machine_fields] >>
  fs[source_typing_ok_def, source_deployment_rel_def,
     checked_contract_runtime_ready_def] >>
  gvs[]
QED

Theorem gas_readings_rel_mono:
  gas_readings_rel readings P T /\ (!gs. P gs ==> Q gs) ==>
  gas_readings_rel readings Q T
Proof
  rw[gas_readings_rel_def] >> metis_tac[]
QED

(* The guarded form: the finite storage guard stays inside the filling. *)
Theorem deploy_call_result_establishes_call_ready:
  deploy_typing_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  supported_program tops /\ supported_program_deploy tops /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  deploy_call_result_rel tops runtime_bc am tx es r es' ==>
  gas_readings_rel (gas_readings es)
    (\gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs ==>
          !am' rqs.
            load_contract (SOME (MAP SND (call_trace es))) gs am tx
              [(NONE, tops)] [] = INL (am', rqs) ==>
            call_ready tops runtime_bc (next_source_machine am' es')
              tx.target) T
Proof
  rw[deploy_call_result_rel_def] >>
  irule gas_readings_rel_mono >> goal_assum (drule_at Any) >>
  rw[] >> irule (INST_TYPE [alpha |-> “:256”] deploy_establishes_call_ready) >>
  rpt (conj_tac >- simp[]) >>
  qexistsl_tac [`storage_trace_horizon (deploy_storage_trace
                   (SOME (MAP SND (call_trace es))) gs am tx tops)`,
                `am`, `deploy_bc`, `es`, `gs`, `SOME (MAP SND (call_trace es))`,
                `r`, `rqs`] >>
  gvs[]
QED

(* ===== Call to call ===== *)

Theorem call_preserves_call_ready:
  call_ready tops runtime_bc am tx.target /\ call_tx_well_typed tx /\
  supported_program tops /\ runtime_bc <> [] /\
  call_state_rel tops runtime_bc am tx es /\ LENGTH es.contexts = 1 /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  call_ready tops runtime_bc (next_source_machine am' es') tx.target
Proof
  strip_tac >>
  `source_typing_ok tops am tx /\ source_deployment_rel tops am tx` by
    fs[call_ready_def] >>
  `am'.immutables = am.immutables` by
    (irule call_external_runtime_preserves_immutables >>
     fs[source_typing_ok_def, source_deployment_rel_def] >> metis_tac[]) >>
  drule call_external_static_fields >> strip_tac >>
  `?ctxt rb rest mr.
     es.contexts = (ctxt, rb) :: rest /\ wf_state es /\
     ctxt.msgParams.outputTo = Memory mr /\
     installed_code_rel tops runtime_bc (account_immutables am tx.target)
       ctxt.msgParams.code /\
     (lookup_account tx.target es.rollback.accounts).code =
       ctxt.msgParams.code` by
    (fs[call_state_rel_def] >> metis_tac[]) >>
  `accounts_well_typed es'.rollback.accounts` by
    (irule run_call_accounts_well_typed >>
     goal_assum $ drule_at Any >> simp[]) >>
  `(lookup_account tx.target es'.rollback.accounts).code =
   (lookup_account tx.target es.rollback.accounts).code` by
    (irule run_call_preserves_installed_code >>
     gvs[installed_code_rel_def] >> metis_tac[]) >>
  simp[call_ready_def] >> conj_tac
  >- (gvs[lookup_account_process_deletions] >> fs[account_immutables_def]) >>
  qx_gen_tac `tx2` >> strip_tac >>
  `source_typing_ok tops am tx2 /\ source_deployment_rel tops am tx2` by
    fs[call_ready_def] >>
  `machine_well_typed (next_source_machine am' es')` by
    (irule next_source_machine_well_typed >>
     fs[source_typing_ok_def, machine_well_typed_def]) >>
  fs[source_typing_ok_def, source_deployment_rel_def, layouts_agree_def,
     checked_contract_runtime_ready_def] >>
  gvs[]
QED

(* ===== Initial storage ===== *)

(* deploy_storage_ok's storage_well_formed_on conjunct at a fresh target. *)
Theorem deploy_empty_storage_well_formed_on:
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage ==>
  storage_well_formed_on (deploy_evaluation_context tops am tx)
    (initial_state am []) regions
Proof
  strip_tac >> irule empty_storage_well_formed_on >>
  Cases >> gvs[get_storage_def, deploy_evaluation_context_def,
               initial_evaluation_context_def, vyperInterpreterTheory.initial_state_def,
               lookup_account_def]
QED

(* ===== Horizon extension ===== *)

(* Storage well-formedness on the next transaction's regions R2: the
   persistent regions it shares with the previous transaction's regions R1
   carry over when the committed storage agrees with the source's off a mask
   D that is dead within every R1 region it touches; the regions new in R2
   are the caller's to supply; transient storage starts empty. *)
Theorem storage_well_formed_on_horizon_extension:
  storage_well_formed_on cx (initial_state am' []) R1 /\
  regions_consistent R1 /\
  storage_agree D (lookup_account cx.txn.target am'.accounts).storage
    (lookup_account cx.txn.target es'.rollback.accounts).storage /\
  (!j b slot tv.
     D j b /\ MEM (F, slot, tv) R1 /\ w2n slot <= j /\
     j < w2n slot + type_slot_size tv ==>
     dead_bytes (lookup_account cx.txn.target am'.accounts).storage
       (w2n slot) tv j b) /\
  ~MEM cx.txn.target es'.rollback.toDelete /\
  cx2.txn.target = cx.txn.target /\
  (!slot tv. MEM (F, slot, tv) R2 /\ ~MEM (F, slot, tv) R1 ==>
     slots_in_range
       (lookup_account cx.txn.target es'.rollback.accounts).storage
       (w2n slot) tv) ==>
  storage_well_formed_on cx2 (initial_state (next_source_machine am' es') [])
    R2
Proof
  rw[storage_well_formed_on_def] >>
  rename1 `MEM (tr, slot, tv) R2` >> Cases_on `tr`
  >- (simp[get_storage_def, vyperInterpreterTheory.initial_state_def, empty_transient_storage_def] >>
      irule (CONJUNCT1 slots_in_range_zero_reads) >>
      simp[read_slot_def, lookup_storage_def, empty_storage_def]) >>
  simp[get_storage_def, vyperInterpreterTheory.initial_state_def] >>
  `(process_deletions es'.rollback.toDelete es'.rollback.accounts
      cx.txn.target).storage =
   (lookup_account cx.txn.target es'.rollback.accounts).storage` by
    simp[GSYM lookup_account_def, lookup_account_process_deletions] >>
  simp[] >>
  Cases_on `MEM (F, slot, tv) R1` >> gvs[] >>
  irule slots_in_range_live_agree >>
  qexists `(lookup_account cx.txn.target am'.accounts).storage` >>
  first_x_assum drule >>
  gvs[get_storage_def, vyperInterpreterTheory.initial_state_def, lookup_account_def,
      regions_consistent_def, storage_agree_def] >>
  reverse conj_tac
  >- (qpat_x_assum `!b slot' tv'. _ ==> slots_in_range _ _ _`
        (qspecl_then [`F`, `slot`, `tv`] mp_tac) >>
      simp[get_storage_def]) >>
  rpt strip_tac >> gvs[] >>
  `~D j b` by metis_tac[] >>
  `type_slot_size tv + w2n slot <= dimword (:256)` by metis_tac[] >>
  `j < dimword (:256)` by decide_tac >>
  first_x_assum (qspec_then `n2w j` mp_tac) >>
  simp[wordsTheory.w2n_n2w]
QED
