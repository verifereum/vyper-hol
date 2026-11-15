(* Source semantics of the final top-level storage-copy write. *)
Theory fullAssignCopyWrite
Ancestors
  vyperStorageBackend vyperStorageFootprint vyperState
  valueEncoding

Theorem topcopy_write_endpoint:
  ~cx.txn.is_static /\ encode_value tv v = SOME writes /\
  value_has_type tv v /\ well_formed_type_value tv /\ ee.gas_obs = [] ==>
  ?ef.
    ef = (set_storage cx ee tr
      (apply_writes (n2w slot) writes (get_storage cx ee tr))) with
      storage_trace := ee.storage_trace ++ [StorageRoot tr slot tv] /\
    (!tail. ignore_bind (record_storage_event (StorageRoot tr slot tv))
       (write_storage_slot cx tr (n2w slot) tv v)
       (ee with gas_obs := tail) = (INL (),ef with gas_obs := tail)) /\
    ef.scopes = ee.scopes /\ ef.gas_obs = [] /\
    get_storage cx ef tr =
      apply_writes (n2w slot) writes (get_storage cx ee tr) /\
    (!H st0. valid_horizon cx st0 H ef.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace) /\
    (!H. regions_consistent (FST H) /\
       MEM (tr,n2w slot,tv) (FST H) /\
       storage_well_formed_on cx ee (FST H) ==>
       storage_well_formed_on cx ef (FST H))
Proof
  strip_tac >>
  qexists_tac `(set_storage cx ee tr
    (apply_writes (n2w slot) writes (get_storage cx ee tr))) with
    storage_trace := ee.storage_trace ++ [StorageRoot tr slot tv]` >>
  `write_storage_slot cx tr (n2w slot) tv v ee =
     (INL (),set_storage cx ee tr
       (apply_writes (n2w slot) writes (get_storage cx ee tr)))` by
    simp[write_storage_slot_eq] >>
  `!H. regions_consistent (FST H) /\
       MEM (tr,n2w slot,tv) (FST H) /\
       storage_well_formed_on cx ee (FST H) ==>
       storage_well_formed_on cx
         (set_storage cx ee tr
           (apply_writes (n2w slot) writes (get_storage cx ee tr))) (FST H)` by
    metis_tac[typed_write_preserves_storage_well_formed_on] >>
  simp[ignore_bind_def, bind_def, return_def, record_storage_event_def,
       write_storage_slot_eq, valid_horizon_def] >>
  conj_tac >- (Cases_on `tr` >> simp[set_storage_def, get_storage_def]) >>
  Cases_on `tr` >> gvs[set_storage_def, get_storage_def,
    storage_well_formed_on_def] >> metis_tac[]
QED
