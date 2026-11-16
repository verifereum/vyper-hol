(* Persistent source worlds between top-level transaction frames. *)
Theory e2eTransactionWorld
Ancestors
  e2eLifecycle e2eDefs vyperRuntimeImmutables vyperInterpreter
  supportedProgram callTrace frameOutcome
  vyperCallFiniteStorage accountsRelProps loweringStateRelDefs
  vyperStorageFootprint vyperLookupStorage vyperStorageBackend vyperStorage
  vfmState vfmExecution

(* A failed top-level frame still contains dirty rollback accounts. *)
Definition transaction_world_def:
  transaction_world am r es' =
    if r = INR NONE then next_source_machine am es' else am
End

(* The selected-filling result of closed_world_call_outcomes_ok. *)
Definition transaction_result_def:
  transaction_result tops ret am tx es r es' <=>
    frame_resource_starved es r es' \/
    gas_readings_rel (gas_readings es)
      (\gs. source_storage_ok am tx (MAP SND (call_trace es)) gs ==>
        call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gs /\
        call_result_rel_at gs tops ret am tx es r es') T
End

Theorem transaction_world_transient_empty:
  am.tStorage a = empty_storage ==>
  (transaction_world am r es').tStorage a = empty_storage
Proof
  rw[transaction_world_def, next_source_machine_def,
     vfmContextTheory.empty_transient_storage_def]
QED

Theorem call_result_rel_at_success_accounts[local]:
  LENGTH es.contexts = 1 /\
  call_external (SOME (MAP SND (call_trace es))) gs am tx = (res, am', rqs) /\
  ~source_exempt tops (call_external (SOME (MAP SND (call_trace es))) gs am tx) /\
  call_result_rel_at gs tops ret am tx es (INR NONE) es' ==>
  accounts_agree
    (storage_trace_horizon (source_storage_trace am tx
      (MAP SND (call_trace es)) gs))
    (initial_evaluation_context am'.sources am'.layouts tx NONE)
    am'.accounts (process_deletions es'.rollback.toDelete es'.rollback.accounts)
Proof
  strip_tac >> namedCases_on `res` ["v", "source_exc"] >>
  gvs[call_result_rel_at_def, call_success_rel_def, LET_THM] >>
  Cases_on `source_exc` >>
  gvs[exception_outcome_rel_def, source_exempt_def, frame_outcome_def,
      AllCaseEqs()]
QED

Theorem call_external_next_source_machine:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  call_external orc gs am tx = (res, am', rqs) ==>
  next_source_machine am' es' = next_source_machine am es'
Proof
  strip_tac >>
  `am'.immutables = am.immutables` by
    (irule call_external_runtime_preserves_immutables >>
     fs[source_typing_ok_def, source_deployment_rel_def] >> metis_tac[]) >>
  drule call_external_static_fields >>
  simp[next_source_machine_def, abstract_machine_component_equality]
QED

Theorem call_preserves_transaction_world:
  call_ready tops runtime_bc am tx.target /\ call_tx_well_typed tx /\
  supported_program tops /\ runtime_bc <> [] /\
  call_state_rel tops runtime_bc am tx es /\ LENGTH es.contexts = 1 /\
  balance_bounded (2 ** 256 - 1) es /\
  run_call es = SOME (r, es') /\ ~MEM tx.target es'.rollback.toDelete ==>
  call_ready tops runtime_bc (transaction_world am r es') tx.target
Proof
  strip_tac >> Cases_on `r = INR NONE` >> simp[transaction_world_def] >>
  `source_typing_ok tops am tx /\ source_deployment_rel tops am tx` by
    fs[call_ready_def] >>
  Cases_on `call_external NONE [] am tx` >>
  rename1 `call_external NONE [] am tx = (res, output)` >>
  PairCases_on `output` >>
  rename1 `call_external NONE [] am tx = (res, am_out, rqs)` >>
  `next_source_machine am_out es' = next_source_machine am es'` by
    (irule call_external_next_source_machine >>
     metis_tac[]) >>
  drule_all call_preserves_call_ready >> simp[]
QED

Theorem transaction_world_storage_handoff:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  call_external_trace (SOME (MAP SND (call_trace es))) gs am tx =
    (res, am', rqs, obs) /\
  H = storage_trace_horizon obs /\
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs /\
  am.tStorage tx.target = empty_storage /\
  LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
  ~source_exempt tops (call_external (SOME (MAP SND (call_trace es))) gs am tx) /\
  (r = INR NONE ==>
    call_result_rel_at gs tops ret am tx es r es' /\
    ~MEM tx.target es'.rollback.toDelete) /\
  cx2.txn.target = tx.target /\
  (!slot tv. MEM (F, slot, tv) R2 /\ ~MEM (F, slot, tv) (FST H) ==>
    slots_in_range
      (lookup_account tx.target (transaction_world am r es').accounts).storage
      (w2n slot) tv) ==>
  storage_well_formed_on cx2 (initial_state (transaction_world am r es') []) R2 /\
  (transaction_world am r es').tStorage tx.target = empty_storage
Proof
  strip_tac >> conj_tac
  >- (Cases_on `r = INR NONE`
      >- (
        `call_result_rel_at gs tops ret am tx es (INR NONE) es' /\
         ~MEM tx.target es'.rollback.toDelete` by metis_tac[] >>
        `call_external (SOME (MAP SND (call_trace es))) gs am tx =
          (res, am', rqs)` by simp[call_external_def] >>
        `source_storage_trace am tx (MAP SND (call_trace es)) gs = obs` by
          simp[source_storage_trace_def] >>
        `next_source_machine am' es' = next_source_machine am es'` by
          (irule call_external_next_source_machine >> metis_tac[]) >>
        `storage_well_formed_on
          (initial_evaluation_context am.sources am.layouts tx NONE)
          (initial_state am' []) (FST H)` by
          (irule call_external_storage_well_formed_on >>
           drule_all source_typing_ok_runtime_ready >> strip_tac >>
           metis_tac[]) >>
        `accounts_agree H
          (initial_evaluation_context am'.sources am'.layouts tx NONE)
          am'.accounts
          (process_deletions es'.rollback.toDelete es'.rollback.accounts)` by
          (drule_all call_result_rel_at_success_accounts >> simp[]) >>
        qabbrev_tac `D = storage_dead H F
          (lookup_account tx.target am'.accounts).storage` >>
        `lookup_account tx.target
           (process_deletions es'.rollback.toDelete es'.rollback.accounts) =
         lookup_account tx.target es'.rollback.accounts` by
          simp[lookup_account_process_deletions] >>
        `storage_agree D (lookup_account tx.target am'.accounts).storage
          (lookup_account tx.target es'.rollback.accounts).storage` by
          fs[accounts_agree_def, initial_evaluation_context_def,
             GSYM lookup_account_def, Abbr `D`] >>
        `!j b slot tv. D j b /\ MEM (F, slot, tv) (FST H) /\
          w2n slot <= j /\ j < w2n slot + type_slot_size tv ==>
          dead_bytes (lookup_account tx.target am'.accounts).storage
            (w2n slot) tv j b` by
          (rw[Abbr `D`] >>
           drule observed_storage_region_read_live >>
           simp[storage_read_live_def] >> metis_tac[]) >>
        `!slot tv. MEM (F, slot, tv) R2 /\ ~MEM (F, slot, tv) (FST H) ==>
          slots_in_range (lookup_account tx.target es'.rollback.accounts).storage
            (w2n slot) tv` by
          fs[transaction_world_def, next_source_machine_def,
             lookup_account_process_deletions] >>
        `regions_consistent (FST H)` by fs[valid_horizon_def] >>
        mp_tac (Q.INST
          [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
           `R1` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`,
           `D` |-> `D`]
          storage_well_formed_on_horizon_extension) >>
        impl_tac >- gvs[initial_evaluation_context_def] >>
        simp[transaction_world_def]) >>
      rw[transaction_world_def, storage_well_formed_on_def] >>
      rename1 `MEM (tr, slot, tv) R2` >> Cases_on `tr`
      >- (simp[get_storage_def, vyperInterpreterTheory.initial_state_def] >>
          irule (CONJUNCT1 slots_in_range_zero_reads) >>
          simp[read_slot_def, lookup_storage_def, empty_storage_def]) >>
      Cases_on `MEM (F, slot, tv) (FST (storage_trace_horizon obs))` >>
      gvs[transaction_world_def, lookup_account_def, get_storage_def,
          vyperInterpreterTheory.initial_state_def]
      >- (fs[valid_horizon_def, storage_well_formed_on_def] >>
          qpat_x_assum `!b slot tv. MEM (b, slot, tv) _ ==> _`
            (qspecl_then [`F`, `slot`, `tv`] mp_tac) >>
          simp[get_storage_def, vyperInterpreterTheory.initial_state_def,
               initial_evaluation_context_def])) >>
  irule transaction_world_transient_empty >> simp[]
QED

Theorem transaction_sequence_call_ready:
  LENGTH worlds = SUC (LENGTH calls) /\
  call_ready tops runtime_bc (HD worlds) a /\
  runtime_bc <> [] /\
  (!i tx ret H es r es'.
    i < LENGTH calls /\ EL i calls = (tx, ret, H, es, r, es') /\
    call_ready tops runtime_bc (EL i worlds) a ==>
    tx.target = a /\ call_tx_well_typed tx /\ supported_program tops /\
    call_state_rel tops runtime_bc (EL i worlds) tx es /\
    LENGTH es.contexts = 1 /\ balance_bounded (2 ** 256 - 1) es /\
    run_call es = SOME (r, es') /\ ~MEM a es'.rollback.toDelete /\
    EL (SUC i) worlds = transaction_world (EL i worlds) r es') ==>
  EVERY (\am. call_ready tops runtime_bc am a) worlds
Proof
  strip_tac >>
  `!i. i < LENGTH worlds ==> call_ready tops runtime_bc (EL i worlds) a` by
    (Induct >- (Cases_on `worlds` >> gvs[]) >> strip_tac >>
     `i < LENGTH calls /\ i < LENGTH worlds` by decide_tac >>
     `call_ready tops runtime_bc (EL i worlds) a` by metis_tac[] >>
     Cases_on `EL i calls` >> rename1 `EL i calls = (tx, tail)` >>
     PairCases_on `tail` >>
     rename1 `EL i calls = (tx, ret, H, es, r, es')` >>
     `tx.target = a /\ call_tx_well_typed tx /\ supported_program tops /\
      call_state_rel tops runtime_bc (EL i worlds) tx es /\
      LENGTH es.contexts = 1 /\ balance_bounded (2 ** 256 - 1) es /\
      run_call es = SOME (r, es') /\ ~MEM a es'.rollback.toDelete /\
      EL (SUC i) worlds = transaction_world (EL i worlds) r es'` by
       metis_tac[] >>
     metis_tac[call_preserves_transaction_world]) >>
  simp[listTheory.EVERY_EL]
QED
