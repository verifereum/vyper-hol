(* Live storage-array source bounds and compiler-header agreement. *)
Theory targetSubscriptStorage
Ancestors
  targetSubscriptMemory targetPlaceLive accountsRelProps exprSimArrayIndex
  vyperState vyperInterpreter vyperValue vyperStorageBackend
  venomState compileEnv context exprLowering exprLoweringProps
  words arithmetic

Theorem extend_place_storage_array_index:
  !cx tr slot et bd i es.
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
      (ValueSubscript (IntV i)) es =
    (case bd of
       Fixed n =>
         if 0 <= i /\ Num i < n then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array fixed oob")), es)
     | Dynamic n =>
         if ~(0 <= i /\ Num i < n) then
           (INR (Error (RuntimeError "array dynamic capacity oob")), es)
         else if Num i < w2n (lookup_storage slot (get_storage cx es tr)) then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (1 + Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array dynamic length oob")), es))
Proof
  rpt gen_tac >> Cases_on `et` >> Cases_on `bd` >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def,
       raise_def, get_storage_backend_eq, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem target_storage_array_len_ok:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (get_storage cx es tr) slot (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  eval_operand base_op s = SOME slot ==>
  array_len_ok T cnt
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (if tr then LocTransient else LocStorage)) base_op s
    (lookup_storage slot (get_storage cx es tr))
Proof
  strip_tac >>
  `storage_range_agree (vyperStorageBackend$get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s)
     slot (ArrayTV tv (Dynamic n))` by
    (irule storage_range_agree_of_live >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, vyperStorageBackendTheory.get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[type_slot_size_def] >>
  drule_all storage_range_agree_head >>
  Cases_on `tr` >> simp[] >> strip_tac
  >- (drule array_len_ok_TLOAD >>
      disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
      simp[tload_def]) >>
  drule array_len_ok_SLOAD >>
  disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
  simp[sload_def]
QED
