(* TOP-LEVEL: resolved-place write boundaries for assignment soundness.
   A typed memory place also needs an assignable root before writing. *)
Theory vyperPlaceWriteSoundness
Ancestors
  list option pair finite_map alist vyperState vyperMisc vyperTyping
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeStatePreservation vyperTypeEnv
  vyperPlaceTyping vyperPlaceFrames vyperLookup vyperAssignPreservesType
  vyperImmutableMetadataFrame[ignore_grammar]

Definition runtime_place_assignable_def:
  runtime_place_assignable st (MemoryPlace id path) =
    (?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable) /\
  runtime_place_assignable st (StoragePlace tr slot tv) = T /\
  runtime_place_assignable st (ImmutablePlace src id path) = T
End

(* Mutable edges are arrays and struct fields. NoneTV is permitted at the
   endpoint; it must not be confused with an invalid path. *)
Definition mutable_place_path_def:
  mutable_place_path tv [] = T /\
  mutable_place_path (ArrayTV tv bd) (ValueSubscript (IntV i)::path) =
    mutable_place_path tv path /\
  mutable_place_path (StructTV fields) (AttrSubscript id::path) =
    (case ALOOKUP fields id of NONE => F | SOME tv => mutable_place_path tv path) /\
  mutable_place_path tv path = F
Termination
  WF_REL_TAC `measure (\(tv,path). LENGTH path)` >> simp[]
End

(* This predicate checks declared metadata, without rechecking dynamic lengths. *)
Definition runtime_place_writable_def:
  runtime_place_writable cx st (MemoryPlace id path) =
    (?entry. lookup_scopes id st.scopes = SOME entry /\ entry.assignable /\
      mutable_place_path entry.type path) /\
  runtime_place_writable cx st (ImmutablePlace src id path) =
    (?imms root a. get_immutables cx src st = (INL imms,st) /\
      FLOOKUP imms id = SOME (root,a) /\
      mutable_place_path root path) /\
  runtime_place_writable cx st (StoragePlace tr slot tv) = T
End

Theorem runtime_place_writable_assignable:
  runtime_place_writable cx st p ==> runtime_place_assignable st p
Proof
  Cases_on `p` >> simp[runtime_place_writable_def, runtime_place_assignable_def] >>
  metis_tac[]
QED

Theorem array_replace_path_no_type_error:
  value_has_type (ArrayTV etv bd) (ArrayV arr) /\ well_formed_type_value etv /\
  (!child err. value_has_type etv child ==>
    assign_subscripts etv child path (Replace nv) <> INR (TypeError err)) ==>
  assign_subscripts (ArrayTV etv bd) (ArrayV arr)
    (ValueSubscript (IntV i)::path) (Replace nv) <> INR (TypeError msg)
Proof
  strip_tac >> simp[Once assign_subscripts_def] >>
  Cases_on `array_index (ArrayTV etv bd) arr i` >> gvs[] >>
  rename1 `array_index (ArrayTV etv bd) arr i = SOME child` >>
  `value_has_type etv child` by
    (irule array_index_has_type >> simp[] >> goal_assum drule >> simp[]) >>
  qpat_x_assum `!child err. _`
    (qspecl_then [`child`,`msg`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `assign_subscripts etv child path (Replace nv)` >> gvs[] >>
  irule array_set_index_no_type_error >> simp[] >> metis_tac[]
QED

Theorem struct_replace_path_no_type_error:
  value_has_type (StructTV fields) (StructV values) /\
  ALOOKUP fields id = SOME ftv /\
  (!child err. value_has_type ftv child ==>
    assign_subscripts ftv child path (Replace nv) <> INR (TypeError err)) ==>
  assign_subscripts (StructTV fields) (StructV values)
    (AttrSubscript id::path) (Replace nv) <> INR (TypeError msg)
Proof
  strip_tac >> Cases_on `ALOOKUP values id`
  >- (gvs[value_has_type_def] >>
      drule_all struct_has_type_alookup_none >> gvs[]) >>
  rename1 `ALOOKUP values id = SOME child` >>
  `value_has_type ftv child` by
    (fs[value_has_type_def] >> drule_all struct_field_has_type >> gvs[]) >>
  qpat_x_assum `!child err. _`
    (qspecl_then [`child`,`msg`] mp_tac) >> simp[] >> strip_tac >>
  simp[Once assign_subscripts_def] >>
  Cases_on `assign_subscripts ftv child path (Replace nv)` >> gvs[]
QED

Theorem well_formed_struct_field_type:
  well_formed_type_value (StructTV fields) /\ ALOOKUP fields id = SOME tv ==>
  well_formed_type_value tv
Proof
  rw[well_formed_type_value_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> strip_tac >>
  qpat_x_assum `!p. MEM p fields ==> _` drule >> simp[combinTheory.o_DEF]
QED

Theorem assign_subscripts_replace_no_type_error:
  !path tv a nv msg.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv ==>
    assign_subscripts tv a path (Replace nv) <> INR (TypeError msg)
Proof
  Induct_on `path` >- simp[Once assign_subscripts_def] >>
  rpt gen_tac >> rename1 `mutable_place_path tv (sb::path)` >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      simp[mutable_place_path_def] >> strip_tac >>
      qmatch_goalsub_rename_tac
        `assign_subscripts (ArrayTV etv bd) a (ValueSubscript (IntV idx)::path)` >>
      `?arr. a = ArrayV arr` by (Cases_on `a` >> gvs[value_has_type_def]) >>
      pop_assum strip_assume_tac >> gvs[] >>
      qmatch_assum_rename_tac `value_has_type (ArrayTV etv bd) (ArrayV arr)` >>
      `well_formed_type_value etv` by fs[well_formed_type_value_def] >>
      irule array_replace_path_no_type_error >> simp[] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!tv a nv msg. _` irule >> simp[]) >>
  Cases_on `tv` >> simp[mutable_place_path_def] >>
  qmatch_goalsub_rename_tac `ALOOKUP fields id` >>
  Cases_on `ALOOKUP fields id` >> simp[] >> strip_tac >>
  qmatch_assum_rename_tac `ALOOKUP fields id = SOME ftv` >>
  `?values. a = StructV values` by (Cases_on `a` >> gvs[value_has_type_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  qmatch_assum_rename_tac `value_has_type (StructTV fields) (StructV values)` >>
  `well_formed_type_value ftv` by
    (drule_all well_formed_struct_field_type >> simp[]) >>
  irule struct_replace_path_no_type_error >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tv a nv msg. _` irule >> simp[]
QED

Theorem write_place_preserves_accounts_well_typed:
  accounts_well_typed st.accounts /\ write_place cx p v st = (res,st') ==>
  accounts_well_typed st'.accounts
Proof
  Cases_on `p` >> rpt strip_tac
  >- (gvs[write_place_def] >>
      drule_all write_storage_slot_preserves_accounts_well_typed >> simp[])
  >- (drule write_memory_place_frame >> strip_tac >> gvs[]) >>
  drule write_immutable_place_frame >> strip_tac >> gvs[]
QED

Theorem write_storage_place_no_type_error:
  value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v st = (res,st') ==>
  no_type_error_result res
Proof
  simp[write_place_def, no_type_error_result_def] >>
  metis_tac[write_storage_slot_no_type_error_from_value_has_type]
QED

(* Both successful replacement and an unobservable stale-slot write retain
   the root's static metadata. Only its value and pop history may change. *)
Theorem replace_memory_entry_metadata:
  replace_memory_entry entry path v = INL entry' ==>
  entry'.type = entry.type /\ entry'.assignable = entry.assignable
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >> gvs[]
QED

Theorem replace_memory_entry_record:
  replace_memory_entry entry path v = INL entry' ==>
  ?w ps. entry' = entry with <|value := w; popped := ps|>
Proof
  strip_tac >> qexistsl_tac [`entry'.value`,`entry'.popped`] >>
  drule replace_memory_entry_metadata >>
  simp[scope_entry_component_equality]
QED

Theorem replace_memory_entry_no_type_error_helper:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  (path = [] \/ leaf_type entry.type path <> NoneTV) ==>
  replace_memory_entry entry path v <> INR (TypeError msg)
Proof
  Cases_on `path = []`
  >- gvs[replace_memory_entry_def, evaluate_subscripts_def, assign_subscripts_def] >>
  simp[] >> strip_tac >>
  `assign_subscripts entry.type entry.value path (Replace v) <> INR (TypeError msg)` by
    (irule assign_subscripts_no_type_error_from_leaf >>
     simp[assign_subscripts_replace_leaf_no_type_error]) >>
  rw[replace_memory_entry_def, AllCaseEqs()] >> gvs[]
QED

Theorem replace_memory_entry_no_type_error:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mutable_place_path entry.type path ==>
  replace_memory_entry entry path v <> INR (TypeError msg)
Proof
  strip_tac >> drule_all assign_subscripts_replace_no_type_error >>
  disch_then (qspecl_then [`v`,`msg`] assume_tac) >>
  rw[replace_memory_entry_def, AllCaseEqs()] >> gvs[]
QED

Theorem write_memory_place_no_type_error:
  state_well_typed st /\ runtime_place_writable cx st (MemoryPlace id path) /\
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `runtime_place_writable _ _ _` mp_tac >>
  simp[NoAsms, runtime_place_writable_def] >> strip_tac >>
  qmatch_assum_rename_tac `lookup_scopes id st.scopes = SOME entry` >>
  `EVERY scope_well_typed st.scopes` by fs[state_well_typed_def] >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  `!msg. replace_memory_entry entry path v <> INR (TypeError msg)` by
    (gen_tac >> irule replace_memory_entry_no_type_error >> simp[]) >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  Cases_on `replace_memory_entry entry path v` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      type_check_def, assert_def, ignore_bind_def, lift_sum_def, set_scopes_def,
      return_def, raise_def, no_type_error_result_def]
QED

Theorem immutable_metadata_frame_sym:
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' ==>
  vyperImmutableMetadataFrame$immutable_metadata_frame st' st
Proof
  rw[immutable_metadata_frame_def] >> metis_tac[]
QED

Theorem immutable_metadata_frame_type_lookup:
  !st st' addr src id.
    vyperImmutableMetadataFrame$immutable_metadata_frame st st' ==>
    OPTION_MAP FST (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables addr of NONE => [] | SOME imms => imms)) id) =
    OPTION_MAP FST (FLOOKUP (get_source_immutables src
      (case ALOOKUP st'.immutables addr of NONE => [] | SOME imms => imms)) id)
Proof
  rpt strip_tac >>
  `IS_SOME (ALOOKUP st.immutables addr) <=>
   IS_SOME (ALOOKUP st'.immutables addr)` by fs[immutable_metadata_frame_def] >>
  Cases_on `ALOOKUP st.immutables addr` >>
  Cases_on `ALOOKUP st'.immutables addr` >> gvs[] >>
  fs[immutable_metadata_frame_def] >>
  qpat_x_assum `!addr imms imms' src id. _`
    (drule_all_then (qspecl_then [`src`,`id`] ACCEPT_TAC))
QED

Theorem immutable_metadata_frame_value_lookup:
  !st st' addr src id tv v.
    vyperImmutableMetadataFrame$immutable_metadata_frame st st' /\
    FLOOKUP (get_source_immutables src
      (case ALOOKUP st'.immutables addr of NONE => [] | SOME imms => imms)) id =
        SOME (tv,v) ==>
    ?old. FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables addr of NONE => [] | SOME imms => imms)) id =
        SOME (tv,old)
Proof
  rpt strip_tac >> drule immutable_metadata_frame_type_lookup >>
  disch_then (qspecl_then [`addr`,`src`,`id`] mp_tac) >>
  simp[OPTION_MAP_EQ_SOME, EXISTS_PROD] >> metis_tac[]
QED

Theorem env_immutables_consistent_metadata_frame:
  env_immutables_consistent env cx st /\
  vyperImmutableMetadataFrame$immutable_metadata_frame st st' ==>
  env_immutables_consistent env cx st'
Proof
  rpt strip_tac >> qpat_x_assum `env_immutables_consistent env cx st` mp_tac >>
  pure_rewrite_tac[env_immutables_consistent_def] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!src id ty. _` drule_all >> strip_tac >>
      drule immutable_metadata_frame_type_lookup >>
      disch_then (qspecl_then [`cx.txn.target`,`src`,`id`] mp_tac) >>
      Cases_on `FLOOKUP (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME imms => imms)) id` >>
      Cases_on `FLOOKUP (get_source_immutables src
        (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME imms => imms)) id` >>
      gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all immutable_metadata_frame_value_lookup >> strip_tac >>
      qpat_x_assum `!src id ty tv v. _` drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!src id ty ts. _` drule_all >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all immutable_metadata_frame_value_lookup >> strip_tac >>
  qpat_x_assum `find_var_decl_by_name id ts = NONE ==> _` drule_all >> simp[]
QED

Theorem write_memory_place_preserves_env_consistent:
  env_consistent env cx st /\
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >> Cases_on `find_containing_scope id st.scopes` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      return_def, raise_def] >>
  rename1 `find_containing_scope id st.scopes = SOME found` >>
  PairCases_on `found` >>
  rename1 `find_containing_scope id st.scopes = SOME (pre,sc,entry,rest)` >>
  gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry entry path v` >> gvs[return_def, raise_def] >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule replace_memory_entry_record >> strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `env_consistent env cx st0` >>
  `st0 with scopes := pre ++ sc::rest = st0` by
    (qpat_x_assum `st0.scopes = _` mp_tac >>
     simp[evaluation_state_component_equality, APPEND_ASSOC]) >>
  irule env_consistent_update_existing_scope_value >> simp[]
QED

Theorem set_immutable_success_from_get:
  get_immutables cx src st = (INL imms,st) /\
  set_immutable cx src id tv v st = (res,st') ==> res = INL ()
Proof
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[get_immutables_def, set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def]
QED

Theorem write_immutable_place_no_type_error:
  state_well_typed st /\ runtime_place_writable cx st (ImmutablePlace src id path) /\
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `runtime_place_writable _ _ _` mp_tac >>
  simp[NoAsms, runtime_place_writable_def] >> strip_tac >>
  qmatch_assum_rename_tac `FLOOKUP imms id = SOME (root,a)` >>
  drule_all get_immutables_success_typed >> strip_tac >>
  `!msg. assign_subscripts root a path (Replace v) <> INR (TypeError msg)` by
    (gen_tac >> irule assign_subscripts_replace_no_type_error >> simp[]) >>
  Cases_on `assign_subscripts root a path (Replace v)` >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [write_place_def, bind_def, lift_option_type_def,
    lift_sum_def, return_def, raise_def] >> strip_tac >>
  FIRST [drule_all set_immutable_success_from_get >> simp[no_type_error_result_def],
         gvs[no_type_error_result_def]]
QED

Theorem write_immutable_place_preserves_env_consistent:
  env_consistent env cx st /\
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >> drule write_immutable_place_scopes >> strip_tac >>
  drule write_place_immutable_metadata_frame >> strip_tac >>
  qpat_x_assum `env_consistent env cx st` mp_tac >>
  pure_rewrite_tac[env_consistent_def] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gvs[env_scopes_consistent_def] >> metis_tac[]) >>
  drule_all env_immutables_consistent_metadata_frame >> simp[]
QED

Theorem write_place_preserves_env_consistent:
  env_consistent env cx st /\ write_place cx p v st = (res,st') ==>
  env_consistent env cx st'
Proof
  Cases_on `p` >> rpt strip_tac
  >- (gvs[write_place_def] >>
      drule_all write_storage_slot_preserves_env_consistent >> simp[])
  >- (drule_all write_memory_place_preserves_env_consistent >> simp[]) >>
  drule_all write_immutable_place_preserves_env_consistent >> simp[]
QED

Theorem write_place_no_type_error:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  runtime_place_writable cx st p /\ value_has_type tv v /\
  write_place cx p v st = (res,st') ==>
  no_type_error_result res
Proof
  Cases_on `p` >> rpt strip_tac
  >- (gvs[runtime_place_typed_storage] >>
      drule_all write_storage_place_no_type_error >> simp[])
  >- (drule_all write_memory_place_no_type_error >> simp[]) >>
  drule_all write_immutable_place_no_type_error >> simp[]
QED

Theorem write_place_sound:
  runtime_consistent env cx st /\ runtime_place_typed cx st p tv /\
  runtime_place_writable cx st p /\ value_has_type tv v /\
  write_place cx p v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  pure_rewrite_tac[runtime_consistent_def] >> strip_tac >>
  drule_all write_place_preserves_state_well_typed >> strip_tac >>
  drule_all write_place_preserves_env_consistent >> strip_tac >>
  drule_all write_place_preserves_accounts_well_typed >> strip_tac >>
  drule_all write_place_no_type_error >> simp[]
QED
