(* Shared boundary facts for whole-run finite storage preservation. *)
Theory vyperCallFiniteStorageSupport
Ancestors
  vyperStorageFootprint vyperStorageBackend vyperInterpreter vyperLookupStorage
  vyperStorage vyperState vfmProg vfmExecution vfmState

Theorem storage_well_formed_on_target:
  cx'.txn.target = cx.txn.target ==>
  (storage_well_formed_on cx' st regions <=>
   storage_well_formed_on cx st regions)
Proof
  strip_tac >>
  `!b. get_storage cx' st b = get_storage cx st b` by
    (Cases_on `b` >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

Theorem storage_observations_ok_target:
  cx'.txn.target = cx.txn.target ==>
  (storage_observations_ok cx' H obs <=> storage_observations_ok cx H obs)
Proof
  strip_tac >>
  `!st (regions : (bool # bytes32 # type_value) list). storage_well_formed_on cx' st regions <=>
                storage_well_formed_on cx st regions` by
    (rpt gen_tac >> irule storage_well_formed_on_target >> simp[]) >>
  `!(regions : (bool # bytes32 # type_value) list). storage_trace_backends_well_formed cx' regions obs <=>
             storage_trace_backends_well_formed cx regions obs` by
    (Induct_on `obs` >- simp[storage_trace_backends_well_formed_def] >>
     qx_gen_tac `ob` >> Cases_on `ob` >>
     simp[storage_trace_backends_well_formed_def]) >>
  rewrite_tac[storage_observations_ok_def] >>
  qpat_x_assum `!regions. storage_trace_backends_well_formed _ _ _ <=> _`
    (qspec_then `FST H` SUBST1_TAC) >> simp[]
QED

(* Committing deletions changes only persistent storage, to zero. *)
Theorem finalize_pending_deletions_preserves_storage_well_formed_on:
  storage_well_formed_on cx (initial_state am []) regions ==>
  storage_well_formed_on cx (initial_state (finalize_pending_deletions am) []) regions
Proof
  rw[storage_well_formed_on_def] >>
  first_x_assum drule >>
  Cases_on `b`
  >- simp[get_storage_def, initial_state_def] >>
  (simp[get_storage_def, initial_state_def] >> strip_tac >>
      Cases_on `MEM cx.txn.target am.pending_deletions`
      >- (simp[finalize_pending_deletions_def,
               GSYM lookup_account_def,
               lookup_account_process_deletions_deleted,
               empty_account_state_def] >>
          irule (CONJUNCT1 slots_in_range_zero_reads) >>
          simp[read_slot_def, lookup_storage_def, empty_storage_def]) >>
      simp[finalize_pending_deletions_def,
           GSYM lookup_account_def,
           lookup_account_process_deletions_other] >>
      simp[lookup_account_def])
QED
