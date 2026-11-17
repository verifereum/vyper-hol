Theory bodyAssignObservedLive
Ancestors
  vyperFiniteStoragePreservation accountsRelProps vyperStoragePlaceObserved
  vyperStorageFootprint loweringStateRelDefs vyperInterpreter vyperTypeSystem
  vyperTypeInvariants vyperValue words arithmetic

Theorem body_assign_observed_storage_read_live:
  !env cx es e H es1 tr slot leaf raw.
    runtime_consistent env cx es /\ well_typed_expr env e /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    valid_horizon cx es H es1.storage_trace /\
    eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot leaf)),es1) ==>
    storage_read_live H tr raw slot leaf
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_slot_size leaf = 0`
  >- simp[storage_read_live_def, wordsTheory.w2n_lt, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all eval_expr_observed_region >> strip_tac >>
  `MEM (tr,n2w offset,tv) (FST H)` by
    (irule storage_observations_ok_root >>
     fs[valid_horizon_def] >> metis_tac[]) >>
  irule storage_place_observed_read_live >>
  simp[storage_place_observed_def] >>
  qexistsl [`n2w offset`, `tv`, `path`, `delta`] >> simp[]
QED
