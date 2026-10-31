Theory vyperPlaceMutationSoundness
Ancestors
  list option pair finite_map vyperState vyperMisc vyperTyping
  vyperTypeInvariants vyperPlaceResultTyping vyperPlaceWriteSoundness
  vyperTypeStatePreservation vyperAssignPreservesType vyperTypeExprSoundness
  vyperPlaceTyping vyperStorageBackend vyperLookup vyperValueOperation
  vyperPlaceStatePreservation vyperPlaceInvariants vyperAbiMutationSoundness
  vyperAbiWriteTyping

Theorem append_nonstorage_place_sound:
  (!tr slot tv. p <> StoragePlace tr slot tv) /\
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of
   | MemoryPlace id path =>
       ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
         memory_eval_path entry.type path /\
         memory_history_region entry fresh old [path]
   | _ => T) /\
  value_has_type etv v /\ append_place cx p v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `state_well_typed st` by gvs[runtime_consistent_def] >>
  `place_type_value cx p st = (INL (ArrayTV etv (Dynamic n)),st)` by
    gvs[runtime_place_typed_def] >>
  Cases_on `read_place cx p st` >>
  rename1 `read_place cx p st = (rr,rs)` >>
  `rs = st` by metis_tac[read_place_preserves_state] >> gvs[] >>
  drule_all read_place_live_typed >> strip_tac >>
  Cases_on `rr` >> gvs[]
  >- (rename1 `read_place cx p st = (INL old,st)` >>
      Cases_on `append_element (ArrayTV etv (Dynamic n)) old v`
      >- (rename1 `append_element _ _ _ = INL updated` >>
          `value_has_type (ArrayTV etv (Dynamic n)) updated` by
            metis_tac[append_element_preserves_type] >>
          drule_all append_nonstorage_updated_sound >> simp[]) >>
      rename1 `append_element _ _ _ = INR err` >>
      `res = INR (Error err) /\ st' = st` by
        (Cases_on `p` >> gvs[append_place_def, bind_def, lift_sum_def, raise_def]) >>
      gvs[no_type_error_result_def] >> metis_tac[append_element_no_type_error]) >>
  rename1 `read_place cx p st = (INR err,st)` >>
  `res = INR err /\ st' = st` by
    (Cases_on `p` >> gvs[append_place_def, bind_def]) >>
  gvs[no_type_error_result_def]
QED

Theorem write_storage_slot_runtime_sound:
  runtime_consistent env cx st /\ well_formed_type_value tv /\
  value_has_type tv v /\ write_storage_slot cx tr slot tv v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  strip_tac >> irule write_place_sound >>
  qexistsl [`StoragePlace tr slot tv`,`st`,`tv`,`v`] >>
  simp[runtime_place_typed_storage, runtime_place_writable_def, write_place_def]
QED

Theorem append_storage_place_sound:
  runtime_consistent env cx st /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\ value_has_type etv v /\
  append_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `well_formed_type_value etv /\ n < 2 ** 256` by
    gvs[well_formed_type_value_def, wordsTheory.dimword_def, SF wordsLib.SIZES_ss] >>
  qpat_x_assum `append_place _ _ _ _ = _` mp_tac >>
  simp[append_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `len < n` >>
  Cases_on `len < n`
  >- (`value_has_type (BaseTV (UintT 256)) (IntV (&(len + 1)))` by
        metis_tac[storage_array_append_len_value_has_type] >>
      simp[] >>
      Cases_on `write_storage_slot cx tr (slot + n2w (len * type_slot_size etv + 1)) etv v st` >>
      rename1 `write_storage_slot _ _ _ _ _ _ = (wr,mid)` >>
      drule_all write_storage_slot_runtime_sound >> strip_tac >>
      Cases_on `wr` >> simp[] >> disch_tac
      >- (drule_at (Pat `write_storage_slot _ _ _ _ _ mid = _`)
            write_storage_slot_runtime_sound >>
          simp[well_formed_type_value_def] >>
          disch_then (qspec_then `env` mp_tac) >> simp[]) >>
      gvs[no_type_error_result_def]) >>
  simp[no_type_error_result_def] >> strip_tac >> gvs[no_type_error_result_def]
QED

Theorem append_place_sound:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of
   | MemoryPlace id path =>
       ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
         memory_eval_path entry.type path /\
         memory_history_region entry fresh old [path]
   | _ => T) /\
  value_has_type etv v /\ append_place cx p v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage] >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all append_storage_place_sound >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule append_nonstorage_place_sound >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem pop_place_valid_scope_trace:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of
   | MemoryPlace id path =>
       ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
         memory_eval_path entry.type path /\
         memory_history_region entry fresh old [path]
   | _ => T) /\
  pop_place cx p st = (res,st') ==>
  ?events. scope_pop_trace st.scopes events st'.scopes /\
    EVERY (\ev. entry_pop_event_valid (SND ev)) events
Proof
  rpt gen_tac >> strip_tac >>
  `state_well_typed st` by gvs[runtime_consistent_def] >>
  Cases_on `p`
  >- (`st'.scopes = st.scopes` by metis_tac[pop_nonmemory_scopes, place_distinct] >>
      qexists_tac `[]` >> simp[scope_pop_trace_def])
  >- (gvs[] >> irule pop_memory_read_typed_trace >> simp[] >>
      qexistsl [`cx`,`s`,`l`,`res`] >> simp[] >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pat `read_memory_path _ _ = _`)
        memory_dynamic_array_authoritative_read >>
      simp[] >> metis_tac[]) >>
  `st'.scopes = st.scopes` by metis_tac[pop_nonmemory_scopes, place_distinct] >>
  qexists_tac `[]` >> simp[scope_pop_trace_def]
QED

Theorem pop_storage_place_sound:
  runtime_consistent env cx st /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\
  pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res /\
  (case res of
   | INL pv => ?q. pv = PlaceR q /\ runtime_place_typed cx st' q etv
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `well_formed_type_value etv` by gvs[well_formed_type_value_def] >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `0 < len` >>
  Cases_on `0 < len`
  >- (`len < 2 ** 256` by
        (simp[Abbr `len`] >>
         mp_tac (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt) >>
         simp[wordsTheory.dimword_def, SF wordsLib.SIZES_ss]) >>
      `value_has_type (BaseTV (UintT 256)) (IntV (&(len - 1)))` by
        metis_tac[storage_array_pop_len_value_has_type] >>
      simp[] >>
      Cases_on `write_storage_slot cx tr slot (BaseTV (UintT 256)) (IntV (&(len - 1))) st` >>
      rename1 `write_storage_slot _ _ _ _ _ _ = (wr,mid)` >>
      `runtime_consistent env cx mid /\ no_type_error_result wr` by
        (irule write_storage_slot_runtime_sound >>
         goal_assum (drule_at Any) >> simp[well_formed_type_value_def]) >>
      Cases_on `wr` >> simp[] >> strip_tac >>
      gvs[no_type_error_result_def, runtime_place_typed_storage]) >>
  simp[] >> strip_tac >> gvs[no_type_error_result_def]
QED

Theorem pop_memory_place_no_type_error:
  state_well_typed st /\
  runtime_place_typed cx st (MemoryPlace id path) (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st (MemoryPlace id path) /\
  (?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
    memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]) /\
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable /\
    mutable_place_path entry.type path` by gvs[runtime_place_writable_def] >>
  gvs[] >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[state_well_typed_def, lookup_scopes_well_typed_value_has_type,
              lookup_scopes_well_typed_type] >>
  `subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n))` by
    gvs[runtime_place_typed_memory] >>
  Cases_on `read_memory_path entry path`
  >- (rename1 `read_memory_path entry path = INL arr` >>
      `value_has_type (ArrayTV etv (Dynamic n)) arr` by
        (drule_at (Pat `read_memory_path _ _ = _`)
           memory_dynamic_array_authoritative_read >> simp[] >> metis_tac[]) >>
      Cases_on `arr` >> gvs[value_has_type_def] >>
      Cases_on `a` >> gvs[value_has_type_def] >>
      `!msg. assign_subscripts entry.type entry.value path
         (Replace (ArrayV (DynArrayV (FRONT l)))) <> INR (TypeError msg)` by
        metis_tac[assign_subscripts_replace_no_type_error] >>
      `!err msg. evaluate_subscripts entry.type entry.value path = INR err ==>
         err <> TypeError msg` by metis_tac[evaluate_subscripts_typed_error] >>
      qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
      simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
           type_check_def, assert_def, check_def, ignore_bind_def, lift_sum_def,
           popped_value_def, pop_element_def, return_def, raise_def] >>
      Cases_on `l = []` >> simp[return_def, raise_def, no_type_error_result_def] >>
      `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV (FRONT l)))` by
        (irule pop_element_preserves_type >> qexists_tac `ArrayV (DynArrayV l)` >>
         simp[pop_element_def, value_has_type_def]) >>
      `IS_SOME (abi_operation_writes (ArrayTV etv (Dynamic n))
         (ArrayV (DynArrayV (FRONT l))) PopOp)` by
        (irule abi_operation_writes_typed >> simp[]) >>
      Cases_on `evaluate_subscripts entry.type entry.value path` >>
      simp[return_def, raise_def] >>
      gvs[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
          AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def,
          no_type_error_result_def] >>
      strip_tac >> gvs[bind_def, set_scopes_def, return_def, raise_def] >>
      qmatch_asmsub_abbrev_tac `write_abi_memory_child _ _ _ _ _ _ before` >>
      drule_all abi_child_writes_success >>
      disch_then (qspecl_then [`cx`,`id`,`before`] strip_assume_tac) >>
      gvs[no_type_error_result_def]) >>
  rename1 `read_memory_path entry path = INR err` >>
  `!msg. err <> TypeError msg` by metis_tac[read_memory_path_typed_error] >>
  gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
      type_check_def, assert_def, ignore_bind_def, lift_sum_def,
      return_def, raise_def, no_type_error_result_def]
QED

Theorem entry_pop_step_value_type:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  entry_pop_event_valid (entry,path) /\ entry_pop_step entry path entry' ==>
  value_has_type entry'.type entry'.value
Proof
  rw[entry_pop_event_valid_def, entry_pop_step_def] >> gvs[] >>
  `value_has_type (ArrayTV etv (Dynamic n)) shortened` by
    metis_tac[pop_element_preserves_type] >>
  metis_tac[vyperPlaceStatePreservationTheory.assign_subscripts_replace_type_metadata]
QED

Theorem runtime_consistent_scope_pop_update:
  runtime_consistent env cx st /\
  find_containing_scope id st.scopes = SOME (pre,frame,entry,rest) /\
  entry_pop_event_valid (entry,path) /\ entry_pop_step entry path next ==>
  runtime_consistent env cx (st with scopes := pre ++ (frame |+ (id,next))::rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    gvs[entry_pop_event_valid_def] >>
  `value_has_type next.type next.value` by metis_tac[entry_pop_step_value_type] >>
  `next.type = entry.type /\ next.assignable = entry.assignable` by
    metis_tac[entry_pop_step_metadata] >>
  `next = entry with <|value := next.value; popped := next.popped|>` by
    simp[scope_entry_component_equality] >>
  `st with scopes := pre ++ frame::rest = st` by
    simp[evaluation_state_component_equality] >>
  gvs[runtime_consistent_def] >> conj_tac
  >- (qpat_assum `next = _` (fn th => once_rewrite_tac[th]) >>
      irule env_consistent_update_existing_scope_value >> simp[]) >>
  gvs[state_well_typed_def, EVERY_APPEND] >>
  qpat_assum `next = _` (fn th => once_rewrite_tac[th]) >>
  irule scope_well_typed_update_value >> simp[]
QED

Theorem runtime_consistent_scope_pop_trace:
  !events st final.
  runtime_consistent env cx st /\ scope_pop_trace st.scopes events final /\
  EVERY (\ev. entry_pop_event_valid (SND ev)) events ==>
  runtime_consistent env cx (st with scopes := final)
Proof
  Induct >- simp[scope_pop_trace_def] >>
  simp[scope_pop_trace_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  gvs[scope_pop_step_def] >>
  drule_all runtime_consistent_scope_pop_update >> strip_tac >>
  first_x_assum drule >> simp[] >>
  disch_then irule >> metis_tac[APPEND, APPEND_ASSOC]
QED

Theorem pop_memory_place_state_frame:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  st' = st with <|scopes := st'.scopes; abi_memory := st'.abi_memory|>
Proof
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def] >>
  Cases_on `find_containing_scope id st.scopes`
  >- (simp[return_def, raise_def] >> strip_tac >> gvs[]) >>
  simp[return_def, raise_def] >>
  PairCases_on `x` >>
  Cases_on `x2.assignable` >>
  simp[type_check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `read_memory_path x2 path` >>
  simp[lift_sum_def, return_def, raise_def] >>
  rename1 `read_memory_path x2 path = INL arr` >>
  Cases_on `arr` >> simp[return_def, raise_def] >>
  Cases_on `a` >> simp[return_def, raise_def] >>
  Cases_on `l = []` >>
  simp[check_def, assert_def, return_def, raise_def] >>
  Cases_on `popped_value (ArrayV (DynArrayV l))` >>
  simp[return_def, raise_def] >>
  Cases_on `pop_element (ArrayV (DynArrayV l))` >>
  simp[return_def, raise_def] >>
  Cases_on `evaluate_subscripts x2.type x2.value path` >>
  simp[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
       AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, write_abi_memory_child_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_component_equality]
QED

Theorem pop_memory_place_sound:
  runtime_consistent env cx st /\
  runtime_place_typed cx st (MemoryPlace id path) (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st (MemoryPlace id path) /\
  (?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
    memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]) /\
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_at (Pat `pop_place _ _ _ = _`) pop_memory_place_state_frame >> strip_tac >>
      `?events. scope_pop_trace st.scopes events st'.scopes /\
         EVERY (\ev. entry_pop_event_valid (SND ev)) events` by
        (irule pop_place_valid_scope_trace >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
      drule_all runtime_consistent_scope_pop_trace >> strip_tac >>
      `runtime_consistent env cx st' <=>
       runtime_consistent env cx (st with scopes := st'.scopes)` by
        (irule runtime_consistent_abi_observations >>
         fs[evaluation_state_component_equality]) >> gvs[]) >>
  irule pop_memory_place_no_type_error >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[runtime_consistent_def]
QED

Theorem pop_memory_place_success:
  pop_place cx (MemoryPlace id path) st = (INL pv,st') ==>
  ?pre frame entry rest vs updated history memory.
    find_containing_scope id st.scopes = SOME (pre,frame,entry,rest) /\
    read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
    pv = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))])) /\
    st' = st with <|scopes := pre ++
      (frame |+ (id,entry with <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history|>))::rest;
      abi_memory := memory|>
Proof
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `find_containing_scope id st.scopes` >>
  simp[return_def, raise_def] >> PairCases_on `x` >>
  Cases_on `x2.assignable` >>
  simp[type_check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `read_memory_path x2 path` >>
  simp[lift_sum_def, return_def, raise_def] >>
  rename1 `read_memory_path x2 path = INL arr` >>
  Cases_on `arr` >> simp[return_def, raise_def] >>
  Cases_on `a` >> simp[return_def, raise_def] >>
  Cases_on `l = []` >>
  simp[check_def, assert_def, popped_value_def, pop_element_def,
       return_def, raise_def] >>
  Cases_on `evaluate_subscripts x2.type x2.value path` >>
  simp[vyperMiscTheory.sum_CASE_rator, vyperMiscTheory.option_CASE_rator,
       AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, write_abi_memory_child_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_component_equality] >>
  metis_tac[]
QED

Theorem popped_child_region:
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value entry.type /\
  value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) /\ vs <> [] ==>
  let child = path ++ [ValueSubscript (IntV &(LENGTH vs - 1))] in
  subscripts_type entry.type child = SOME etv /\
  memory_history_region
    (entry with <|value := updated;
      popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history|>)
    [(child,LAST vs)] history [child]
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  `LENGTH vs - 1 < n` by (gvs[value_has_type_def] >> Cases_on `vs` >> gvs[]) >>
  `subscripts_type entry.type
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME etv` by
    (drule vyperPlaceResultTypingTheory.subscripts_type_append >>
     disch_then (qspec_then `[ValueSubscript (IntV &(LENGTH vs - 1))]` mp_tac) >>
     simp[subscripts_type_def, subscript_type_def, vyperASTTheory.bound_length_def]) >>
  `well_formed_type_value etv` by metis_tac[subscripts_type_well_formed] >>
  `value_has_type etv (LAST vs)` by
    (gvs[value_has_type_def, all_have_type_EVERY] >>
     metis_tac[EVERY_MEM, rich_listTheory.MEM_LAST_NOT_NIL]) >>
  simp[memory_history_region_def, record_pop_def, popped_history_typed_def,
       memory_path_covered_def, read_popped_def, evaluate_subscripts_def]
QED

Theorem pop_memory_place_result_typed:
  runtime_consistent env cx st /\
  runtime_place_typed cx st (MemoryPlace id path) (ArrayTV etv (Dynamic n)) /\
  (?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
    memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]) /\
  pop_place cx (MemoryPlace id path) st = (INL pv,st') ==>
  ?id' path' entry' fresh' old'.
    pv = PlaceR (MemoryPlace id' path') /\
    runtime_place_typed cx st' (MemoryPlace id' path') etv /\
    lookup_scopes id' st'.scopes = SOME entry' /\
    memory_eval_path entry'.type path' /\
    memory_history_region entry' fresh' old' [path']
Proof
  rpt gen_tac >> strip_tac >>
  drule pop_memory_place_success >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >> gvs[] >>
  `state_well_typed st` by gvs[runtime_consistent_def] >>
  `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule_at (Pat `read_memory_path _ _ = _`)
       memory_dynamic_array_authoritative_read >> simp[] >> metis_tac[]) >>
  `subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n))` by
    gvs[runtime_place_typed_memory] >>
  `well_formed_type_value entry.type` by
    metis_tac[state_well_typed_def, lookup_scopes_well_typed_type] >>
  drule_all popped_child_region >> simp[] >> strip_tac >>
  `lookup_scopes id (pre ++
      (frame |+ (id,entry with <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history|>))::rest) =
    SOME (entry with <|value := updated;
      popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history|>)` by
    (drule_all lookup_scopes_update_existing_value_at_found_scope >> simp[]) >>
  simp[runtime_place_typed_memory, memory_eval_path_def] >>
  metis_tac[subscripts_type_well_formed]
QED

Theorem pop_immutable_place_sound:
  runtime_consistent env cx st /\
  runtime_place_typed cx st (ImmutablePlace src id path) (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st (ImmutablePlace src id path) /\
  pop_place cx (ImmutablePlace src id path) st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res /\
  (case res of INL pv => ?v. pv = Value v /\ value_has_type etv v | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `state_well_typed st` by gvs[runtime_consistent_def] >>
  qpat_assum `runtime_place_typed _ _ _ _` mp_tac >>
  simp[NoAsms, runtime_place_typed_immutable] >> strip_tac >>
  rename1 `FLOOKUP imms id = SOME (root,a)` >>
  drule_all get_immutables_success_typed >> strip_tac >>
  Cases_on `evaluate_subscripts root a path`
  >- (rename1 `evaluate_subscripts root a path = INL arr` >>
      `value_has_type (ArrayTV etv (Dynamic n)) arr` by
        metis_tac[evaluate_subscripts_type] >>
      Cases_on `arr` >> gvs[value_has_type_def] >>
      Cases_on `a'` >> gvs[value_has_type_def] >>
      Cases_on `l = []`
      >- (gvs[pop_place_def, bind_def, lift_option_type_def, lift_sum_def,
              popped_value_def, return_def, raise_def, no_type_error_result_def]) >>
      `assign_subscripts root a path PopOp =
       assign_subscripts root a path (Replace (ArrayV (DynArrayV (FRONT l))))` by
        (irule assign_subscripts_pop_replace >>
         qexists_tac `ArrayV (DynArrayV l)` >> simp[pop_element_def]) >>
      `value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV (FRONT l)))` by
        (irule pop_element_preserves_type >>
         qexists_tac `ArrayV (DynArrayV l)` >> simp[pop_element_def, value_has_type_def]) >>
      Cases_on `write_place cx (ImmutablePlace src id path)
         (ArrayV (DynArrayV (FRONT l))) st` >>
      rename1 `write_place _ _ _ _ = (wr,mid)` >>
      `runtime_consistent env cx mid /\ no_type_error_result wr` by
        (irule write_place_sound >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
      `value_has_type etv (LAST l)` by
        (gvs[all_have_type_EVERY] >> metis_tac[EVERY_MEM, rich_listTheory.MEM_LAST_NOT_NIL]) >>
      qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
      Cases_on `wr` >>
      gvs[pop_place_def, write_place_def, bind_def, ignore_bind_def,
          lift_option_type_def, lift_sum_def, popped_value_def,
          return_def, raise_def, no_type_error_result_def] >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[AllCaseEqs(), no_type_error_result_def] >>
      imp_res_tac write_abi_immutables_runtime_frame >> gvs[] >>
      drule_all pop_abi_immutables_replace_no_type_error >>
      gvs[no_type_error_result_def]) >>
  rename1 `evaluate_subscripts root a path = INR err` >>
  `!msg. err <> TypeError msg` by metis_tac[evaluate_subscripts_typed_error] >>
  gvs[pop_place_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, no_type_error_result_def]
QED

Theorem pop_place_sound:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of MemoryPlace id path =>
     ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
       memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]
   | _ => T) /\
  pop_place cx p st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage] >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all pop_storage_place_sound >> simp[])
  >- (simp[] >> metis_tac[pop_memory_place_sound]) >>
  simp[] >> metis_tac[pop_immutable_place_sound]
QED

Theorem pop_place_result_typed:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of MemoryPlace id path =>
     ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
       memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]
   | _ => T) /\
  pop_place cx p st = (INL pv,st') ==>
  (case pv of Value v => value_has_type etv v
   | PlaceR q => runtime_place_typed cx st' q etv
   | HashMapRef _ _ _ _ => F)
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage] >> rpt gen_tac >> strip_tac >> gvs[] >>
      drule_all pop_storage_place_sound >> simp[] >> strip_tac >> gvs[])
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      drule_at (Pat `pop_place _ _ _ = _`) pop_memory_place_result_typed >>
      disch_then (qspecl_then [`n`,`etv`,`env`] mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >> strip_tac >> gvs[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all pop_immutable_place_sound >> simp[] >> strip_tac >> gvs[]
QED

Theorem pop_place_result_live:
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\
  (case p of MemoryPlace id path =>
     ?entry fresh old. lookup_scopes id st.scopes = SOME entry /\
       memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]
   | _ => T) /\
  pop_place cx p st = (INL (PlaceR q),st') ==>
  (case q of MemoryPlace id path =>
     ?entry fresh old. lookup_scopes id st'.scopes = SOME entry /\
       memory_eval_path entry.type path /\ memory_history_region entry fresh old [path]
   | _ => T)
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage] >> rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
      simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
           check_def, assert_def, return_def, raise_def] >>
      rpt strip_tac >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def])
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      drule_at (Pat `pop_place _ _ _ = _`) pop_memory_place_result_typed >>
      disch_then (qspecl_then [`n`,`etv`,`env`] mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all pop_immutable_place_sound >> simp[]
QED
