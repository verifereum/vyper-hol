(*
 * Whole-run finite storage preservation: a checked external call, and a
 * checked constructor run, keep every region of a valid horizon in range.
 *)
Theory vyperCallFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperTypeSelectedEntry
  vyperTypeExternalCallMachine vyperTypeExternalDefaults
  vyperTypeDeploymentMachine vyperTypeContractSoundness vyperLookupStorage
  vyperStorage vyperStorageBackend vyperState vyperInterpreter vyperContext
  vyperCall vyperStorageTrace vyperTypeInvariants vfmState
  vyperCallFiniteStorageSupport vyperExternalDefaultsFiniteStorage
  vyperGetterFiniteStorage vyperExternalBodyFiniteStorage

val _ = Parse.hide "body";

(* Intuition: storage_well_formed_on reads only cx.txn.target, so the
   NONE-module context and the selected module's context agree. Lookup and
   binding failures return am unchanged. Otherwise the body runs from a state
   with am's accounts and tStorage (the value transfer moves balances only),
   set up by checked_explicit_external_body_setup (getters likewise) or
   checked_constructor_body_setup, with call_evaluation_safe from
   checked_*_body_call_evaluation_safe; eval_storage_well_formed_on_mutual
   carries the horizon through the body, its observations being a prefix of
   obs. finalize_pending_deletions only empties accounts, and empty storage
   is in range. *)

(* Zero storage decodes on every region. *)
Theorem empty_storage_well_formed_on:
  (!b. get_storage cx st b = empty_storage) ==>
  storage_well_formed_on cx st regions
Proof
  rw[storage_well_formed_on_def] >>
  irule (CONJUNCT1 slots_in_range_zero_reads) >>
  simp[read_slot_def, lookup_storage_def, empty_storage_def]
QED

Theorem call_external_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  call_external_trace orc gobs am tx = (res,am',rqs,obs) /\
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs ==>
  storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am' []) (FST H)
Proof
  strip_tac >>
  Cases_on `?exc. res = INR exc /\ exc <> HaltException`
  >- (gvs[] >>
      `call_external orc gobs am tx = (INR exc,am',rqs)` by
        simp[call_external_def] >>
      `am' = am` by metis_tac[call_external_error_rollback] >>
      gvs[valid_horizon_def]) >>
  qpat_x_assum `call_external_trace _ _ _ _ = _` mp_tac >>
  simp[Once call_external_trace_def] >>
  gvs[checked_contract_runtime_ready_def] >>
  FAIL_TAC "selected wrapper"
QED

Theorem load_contract_storage_well_formed_on:
  machine_well_typed am /\
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  context_well_typed
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T) /\
  load_contract_trace orc gobs am tx mods exps = (INL (am',rqs),obs) /\
  valid_horizon
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T)
    (initial_state am []) H obs ==>
  storage_well_formed_on
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T)
    (initial_state am' []) (FST H)
Proof
  cheat
QED
