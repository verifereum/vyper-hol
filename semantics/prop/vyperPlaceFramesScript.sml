Theory vyperPlaceFrames
Ancestors
  list rich_list pair finite_map alist vyperState vyperStorageBackend
  vyperScopePreservation vyperImmutablesPreservation vyperStatePreservation

Theorem write_storage_place_eq:
  write_place cx (StoragePlace tr slot tv) v st =
    if cx.txn.is_static then
      (INR (Error (RuntimeError "write in static context")), st)
    else
    (case encode_value tv v of
     | SOME writes =>
         (INL (), set_storage cx st tr
           (apply_writes slot writes (get_storage cx st tr)))
     | NONE => (INR (Error (TypeError "write_storage_slot encode")), st))
Proof
  simp[write_place_def, write_storage_slot_eq]
QED

Theorem write_storage_place_scopes:
  write_place cx (StoragePlace tr slot tv) v st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  simp[write_place_def] >> metis_tac[write_storage_slot_scopes]
QED

Theorem write_storage_place_immutables:
  write_place cx (StoragePlace tr slot tv) v st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  simp[write_place_def] >> metis_tac[write_storage_slot_immutables]
QED

Theorem write_memory_place_frame:
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  ?sc. st' = st with scopes := sc
Proof
  simp[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, UNCURRY] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
           lift_sum_def, set_scopes_def, return_def, raise_def]) >>
  rpt strip_tac >> qexists `st'.scopes` >> gvs[]
QED

Theorem write_immutable_place_state_frame:
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  ?imms history. st' = st with <|immutables := imms; immutable_popped := history|>
Proof
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
           lift_sum_def, set_scopes_def, return_def, raise_def]) >>
  rpt strip_tac >> qexistsl_tac [`st'.immutables`, `st'.immutable_popped`] >>
  gvs[evaluation_state_component_equality]
QED

Theorem write_place_logs:
  write_place cx p v st = (res,st') ==> st'.logs = st.logs
Proof
  Cases_on `p`
  >- (simp[write_storage_place_eq] >>
      Cases_on `cx.txn.is_static` >> Cases_on `encode_value t v` >> simp[] >>
      rpt strip_tac >> gvs[])
  >- (strip_tac >> drule write_memory_place_frame >> strip_tac >> gvs[]) >>
  strip_tac >> drule write_immutable_place_state_frame >> strip_tac >> gvs[]
QED

Theorem write_memory_place_immutables:
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  strip_tac >> drule write_memory_place_frame >> strip_tac >> gvs[]
QED

Theorem write_immutable_place_scopes:
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  strip_tac >> drule write_immutable_place_state_frame >> strip_tac >> gvs[]
QED

Theorem write_memory_place_storage:
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >> drule write_memory_place_frame >> strip_tac >>
  gvs[get_storage_scopes]
QED

Theorem write_immutable_place_storage:
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >> drule write_immutable_place_state_frame >> strip_tac >>
  Cases_on `b` >> gvs[get_storage_def]
QED

Theorem write_place_immutables_addr_dom:
  write_place cx p v st = (res,st') ==>
  !addr. IS_SOME (ALOOKUP st'.immutables addr) =
         IS_SOME (ALOOKUP st.immutables addr)
Proof
  Cases_on `p`
  >- (metis_tac[write_storage_place_immutables])
  >- (metis_tac[write_memory_place_immutables]) >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `cx.txn.target = addr` >>
  gvs[ALOOKUP_ADELKEY]
QED

Theorem write_place_immutables_dom:
  write_place cx p v st = (res,st') /\
  ALOOKUP st.immutables cx.txn.target = SOME imms /\
  ALOOKUP st'.immutables cx.txn.target = SOME imms' ==>
  !src id. IS_SOME (FLOOKUP (get_source_immutables src imms') id) =
           IS_SOME (FLOOKUP (get_source_immutables src imms) id)
Proof
  Cases_on `p`
  >- (metis_tac[write_storage_place_immutables, optionTheory.SOME_11])
  >- (metis_tac[write_memory_place_immutables, optionTheory.SOME_11]) >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  simp[set_source_immutables_def, get_source_immutables_def,
       ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[get_source_immutables_def, FLOOKUP_UPDATE])
QED

Theorem extend_storage_place_state:
  extend_storage_place cx tr slot tv sb st = (res,st') ==> st' = st
Proof
  Cases_on `sb`
  >- (Cases_on `v` >> Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, return_def, raise_def,
           ignore_bind_def, check_def, assert_def, lift_option_type_def,
           UNCURRY] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      metis_tac[resolve_array_element_state]) >>
  Cases_on `tv` >>
  simp[extend_storage_place_def, bind_def, lift_option_type_def,
       return_def, raise_def, UNCURRY] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem extend_place_state:
  extend_place cx res sb st = (result,st') ==> st' = st
Proof
  Cases_on `res`
  >- simp[extend_place_def, raise_def]
  >- (Cases_on `p`
      >- (simp[extend_place_def, bind_def, return_def, raise_def] >>
          Cases_on `extend_storage_place cx b c t sb st` >>
          rename1 `extend_storage_place _ _ _ _ _ _ = (outcome,tmp)` >>
          drule extend_storage_place_state >> strip_tac >> gvs[] >>
          Cases_on `outcome` >> simp[]) >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def] >>
      qmatch_goalsub_abbrev_tac `place_type_value cx p st` >>
      Cases_on `place_type_value cx p st` >>
      rename1 `place_type_value _ _ _ = (outcome,tmp)` >>
      drule place_type_value_state >> strip_tac >> gvs[] >>
      Cases_on `outcome` >> gvs[return_def, raise_def] >>
      qmatch_goalsub_rename_tac `read_place cx p state` >>
      Cases_on `read_place cx p state` >>
      rename1 `read_place _ _ _ = (outcome,tmp)` >>
      drule read_place_state >> strip_tac >> gvs[] >>
      Cases_on `outcome` >> gvs[return_def, raise_def] >>
      simp[lift_sum_def] >>
      qmatch_goalsub_rename_tac `evaluate_subscripts tv value subs` >>
      Cases_on `evaluate_subscripts tv value subs` >>
      simp[return_def, raise_def]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])
QED

Theorem select_result_state:
  select_result cx ty res sb st = (result,st') ==> st' = st
Proof
  Cases_on `res` >>
  simp[select_result_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[extend_place_state]
QED

Theorem get_place_state:
  get_place pv st = (res,st') ==> st' = st
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def]
QED

(* Fail the build if a frame boundary acquires an admitted dependency. *)
val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("vyperPlaceFrames." ^ name ^ ": admitted dependency")
  end) (DB.thms "vyperPlaceFrames");
