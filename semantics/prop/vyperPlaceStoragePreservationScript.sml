(* Memory and immutable place operations preserve the storage backends. *)
Theory vyperPlaceStoragePreservation
Ancestors
  arithmetic words vyperState vyperTyping vyperStorageBackend
  vyperStorageLayoutSafety vyperStorageWritePreservation
  vyperStoragePlaceRegion vyperStorageRegionWrite vyperStoragePlaceProvenance
  vyperPlaceTyping vyperPlaceFrames vyperTypeStoragePreservation
Libs
  wordsLib

Theorem append_memory_place_storage:
  append_place cx (MemoryPlace id path) v st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[append_place_def, bind_def] >>
  Cases_on `place_type_value cx (MemoryPlace id path) st` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  rename1 `place_type_value cx (MemoryPlace id path) s = (INL tv,s)` >>
  Cases_on `read_place cx (MemoryPlace id path) s` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  simp[lift_sum_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[write_memory_place_storage]
QED

Theorem append_immutable_place_storage:
  append_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[append_place_def, bind_def] >>
  Cases_on `place_type_value cx (ImmutablePlace src id path) st` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  rename1 `place_type_value cx (ImmutablePlace src id path) s = (INL tv,s)` >>
  Cases_on `read_place cx (ImmutablePlace src id path) s` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  simp[lift_sum_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[write_immutable_place_storage]
QED

Theorem pop_memory_place_storage:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, ignore_bind_def, check_def, pairTheory.UNCURRY] >>
  Cases_on `find_containing_scope id st.scopes`
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[return_def] >>
  reverse (Cases_on `x2.assignable`)
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >>
  reverse (Cases_on `read_memory_path x2 path`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[return_def] >> rename1 `popped_value arr` >>
  Cases_on `(case arr of ArrayV (DynArrayV vs) => SOME vs | _ => NONE)`
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[return_def] >>
  rename1 `LENGTH vs` >>
  Cases_on `vs = []`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >>
  reverse (Cases_on `popped_value arr`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[return_def] >>
  reverse (Cases_on `pop_element arr`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[return_def] >>
  (* The update/history calculation is pure; split its result as a whole. *)
  qmatch_goalsub_abbrev_tac
    `(case update of INL v => return v | INR e => raise (Error e))` >>
  reverse (Cases_on `update`)
  >- (simp[raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[return_def] >> rpt strip_tac >> gvs[get_storage_scopes]
QED

Theorem pop_immutable_place_storage:
  pop_place cx (ImmutablePlace src id path) st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[pop_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, return_def, raise_def,
       ignore_bind_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> Cases_on `tr` >> gvs[get_storage_def]
QED
