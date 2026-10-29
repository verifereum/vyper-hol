(*
 * State-update preservation lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeStatePreservation
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperStorageBackend vyperLookup vyperEncodeDecode vyperArith vyperAssignPreservesType
  vyperTypeSystem vyperTypeInvariants vyperTypeValues vyperTypeDefaults
  vyperScopePreservation vyperImmutablesPreservation vyperLookupStorage
  vyperStatePreservation vyperTypeEnv vyperTypeEnvPreservation vyperTypeABI vyperTypeBuiltins vyperTypeExprSoundness vyperEvalPreservesScopes
Libs
  wordsLib markerLib

(* ===== Scope operations ===== *)

Theorem push_scope_preserves_state_well_typed:
  state_well_typed st /\ push_scope st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[push_scope_def, return_def, state_well_typed_def, scope_well_typed_def] >>
  rw[] >> rw[scope_well_typed_def]
QED

Theorem pop_scope_preserves_state_well_typed:
  state_well_typed st /\ pop_scope st = (INL u, st') ==>
  state_well_typed st'
Proof
  Cases_on `st.scopes` >>
  rw[pop_scope_def, return_def, raise_def, state_well_typed_def] >>
  rw[]
QED

Theorem push_scope_with_var_preserves_state_well_typed:
  state_well_typed st /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ push_scope_with_var id tv v st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[push_scope_with_var_def, return_def, state_well_typed_def,
     scope_well_typed_def] >> rw[] >>
  rw[scope_well_typed_def] >> gvs[FLOOKUP_UPDATE] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem new_variable_preserves_state_well_typed:
  state_well_typed st /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ new_variable id tv v st = (INL u, st') ==>
  state_well_typed st'
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, AllCaseEqs(), LET_THM,
     state_well_typed_def, scope_well_typed_def, list_CASE_rator,
     assert_def] >> gvs[scope_well_typed_def, FLOOKUP_UPDATE] >>
  rw[] >> rw[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem new_variable_preserves_state_well_typed_result:
  state_well_typed st /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ new_variable id tv v st = (res, st') ==>
  state_well_typed st'
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, AllCaseEqs(), LET_THM,
     state_well_typed_def, scope_well_typed_def, list_CASE_rator,
     assert_def] >> gvs[scope_well_typed_def, FLOOKUP_UPDATE] >>
  rw[] >> rw[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem new_variable_accounts:
  new_variable id tv v st = (res, st') ==> st'.accounts = st.accounts
Proof
  rw[new_variable_def, bind_apply, ignore_bind_apply, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, assert_def, AllCaseEqs(),
     LET_THM, list_CASE_rator] >> gvs[]
QED

Theorem new_variable_no_type_error:
  env_consistent env cx st /\ id NOTIN FDOM env.var_types /\
  new_variable id tv v st = (INR (Error e), st') ==>
  !msg. e <> TypeError msg
Proof
  rw[new_variable_def, bind_apply, ignore_bind_apply, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, assert_def, AllCaseEqs(),
     LET_THM, list_CASE_rator] >>
  gvs[env_consistent_def, env_scopes_consistent_def, optionTheory.IS_SOME_EXISTS, TO_FLOOKUP] >>
  Cases_on `lookup_scopes id st.scopes` >> gvs[] >>
  qpat_x_assum `!id entry. lookup_scopes id st.scopes = SOME entry ==> _`
    (qspecl_then [`id`, `x`] mp_tac) >> simp[TO_FLOOKUP]
QED

(* ===== Storage/account/immutable operations ===== *)

Theorem read_storage_slot_preserves_state_well_typed:
  state_well_typed st /\ read_storage_slot cx is_transient slot tv st = (INL v, st') ==>
  state_well_typed st'
Proof
  Cases_on `is_transient` >>
  rw[read_storage_slot_def, get_storage_backend_def, get_transient_storage_def,
     get_accounts_def, bind_def, return_def, raise_def, lift_option_def,
     AllCaseEqs(), option_CASE_rator] >> gvs[]
QED

(* ===== Leaf helpers needed by assignment/materialisation preservation ===== *)

Theorem decode_base_from_slot_well_typed:
  !slot tv. well_formed_type_value tv /\
    (!n. tv <> BaseTV (StringT n)) /\
    (!n. tv <> BaseTV (BytesT (Dynamic n))) /\
    (!tvs. tv <> TupleTV tvs) /\
    (!tv0 b. tv <> ArrayTV tv0 b) /\
    (!fs. tv <> StructTV fs) ==>
    value_has_type tv (decode_base_from_slot slot tv)
Proof
  ho_match_mp_tac decode_base_from_slot_ind >>
  simp[decode_base_from_slot_def, value_has_type_inv,
       well_formed_type_value_def,
       truncate_unsigned_range,
       word_to_bytes_be_def, LENGTH_word_to_bytes,
       LENGTH_TAKE_EQ, MIN_DEF] >>
  rw[] >> irule truncate_signed_range >> simp[]
QED

Theorem slots_to_bytes_length:
  !n slots. LENGTH (slots_to_bytes n slots) <= n
Proof
  ho_match_mp_tac slots_to_bytes_ind >>
  rw[slots_to_bytes_def, word_to_bytes_be_def, LENGTH_word_to_bytes,
     LET_THM, LENGTH_TAKE_EQ, MIN_DEF, LENGTH_APPEND]
QED

Theorem decode_dyn_bytes_length:
  !storage offset max bs.
    decode_dyn_bytes storage offset max = SOME bs ==> LENGTH bs <= max
Proof
  simp[decode_dyn_bytes_def, LET_THM] >> rpt strip_tac >>
  irule LESS_EQ_TRANS >> qexists_tac `w2n (lookup_storage (n2w offset) storage)` >>
  simp[slots_to_bytes_length]
QED

Theorem enumerate_static_array_sparse_has_type:
  !tv vs n.
    all_have_type tv vs ==>
    sparse_has_type tv (n + LENGTH vs)
      (enumerate_static_array (default_value tv) n vs)
Proof
  Induct_on `vs` >>
  simp[enumerate_static_array_def, value_has_type_def, LET_THM] >>
  rpt strip_tac >>
  IF_CASES_TAC >> gvs[value_has_type_def, ADD1]
  >- (first_x_assum $ qspecl_then [`tv`, `SUC n`] mp_tac >> simp[ADD1]) >>
  simp[] >>
  first_x_assum $ qspecl_then [`tv`, `SUC n`] mp_tac >> simp[ADD1]
QED

Theorem decode_static_array_length:
  !storage offset tv n vs.
    decode_static_array storage offset tv n = SOME vs ==>
    LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

Theorem decode_dyn_array_length:
  !storage offset tv n vs.
    decode_dyn_array storage offset tv n = SOME vs ==>
    LENGTH vs = n
Proof
  Induct_on `n` >>
  simp[Once decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

Theorem decode_value_well_typed:
  (!storage offset tv v.
     decode_value storage offset tv = SOME v /\
     well_formed_type_value tv ==> value_has_type tv v) /\
  (!storage offset tvs vs.
     decode_tuple storage offset tvs = SOME vs /\
     EVERY well_formed_type_value tvs ==> values_have_types tvs vs) /\
  (!storage offset tv n vs.
     decode_static_array storage offset tv n = SOME vs /\
     well_formed_type_value tv ==> all_have_type tv vs) /\
  (!storage offset tv n vs.
     decode_dyn_array storage offset tv n = SOME vs /\
     well_formed_type_value tv ==> all_have_type tv vs) /\
  (!storage offset ftypes fields.
     decode_struct storage offset ftypes = SOME fields /\
     EVERY (well_formed_type_value o SND) ftypes ==>
     struct_has_type ftypes fields)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >>
  simp[decode_value_def, AllCaseEqs(), value_has_type_inv,
       well_formed_type_value_def, value_has_type_def, PULL_EXISTS,
       decode_base_from_slot_well_typed] >>
  rpt strip_tac >> gvs[]
  >- (metis_tac[decode_dyn_bytes_length])
  >- (metis_tac[decode_dyn_bytes_length])
  >- (first_x_assum irule >> gvs[EVERY_MEM])
  >- simp[enumerate_static_array_sorted]
  >- (qpat_x_assum `decode_static_array _ _ _ _ = _`
        (ASSUME_TAC o MATCH_MP decode_static_array_length) >>
      gvs[] >>
      irule (enumerate_static_array_sparse_has_type
             |> Q.SPECL [`tv`,`vs`,`0`]
             |> SIMP_RULE (srw_ss()) []) >>
      simp[])
  >- (qpat_x_assum `decode_dyn_array _ _ _ _ = _`
        (ASSUME_TAC o MATCH_MP decode_dyn_array_length) >>
      gvs[MIN_DEF])
  >> (first_x_assum irule >> gvs[EVERY_MEM])
QED

Theorem read_storage_slot_success_type:
  well_formed_type_value tv /\
  read_storage_slot cx is_transient slot tv st = (INL v, st') ==>
  value_has_type tv v
Proof
  simp[read_storage_slot_def, bind_def, AllCaseEqs(), get_storage_backend_def,
       return_def, lift_option_def, option_CASE_rator, raise_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all (cj 1 decode_value_well_typed) >> simp[]
QED

Theorem scope_well_typed_update_value:
  scope_well_typed sc /\ FLOOKUP sc n = SOME entry /\ value_has_type entry.type v ==>
  scope_well_typed (sc |+ (n, entry with <|value := v; popped := ps|>))
Proof
  rw[scope_well_typed_def, FLOOKUP_UPDATE] >>
  Cases_on `n = id` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem lookup_scopes_well_typed_value_has_type:
  !scopes n entry.
    EVERY scope_well_typed scopes /\ lookup_scopes n scopes = SOME entry ==>
    value_has_type entry.type entry.value
Proof
  Induct >> simp[lookup_scopes_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `FLOOKUP h n` >> gvs[scope_well_typed_def] >>
  metis_tac[]
QED

Theorem lookup_scopes_state_well_typed_value_has_type:
  state_well_typed st /\ lookup_scopes n st.scopes = SOME entry ==>
  value_has_type entry.type entry.value
Proof
  rw[state_well_typed_def] >>
  drule_all lookup_scopes_well_typed_value_has_type >> simp[]
QED

Theorem lookup_scopes_update_existing_value_at_found_scope:
  !pre sc rest n entry v.
    lookup_scopes n pre = NONE /\ FLOOKUP sc n = SOME entry ==>
    lookup_scopes n (pre ++ (sc |+ (n, entry with <|value := v; popped := ps|>))::rest) =
    SOME (entry with <|value := v; popped := ps|>) /\
    lookup_scopes n (pre ++ sc::rest) = SOME entry
Proof
  Induct >> simp[lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `FLOOKUP h n` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem lookup_scopes_update_existing_value_other:
  !pre sc rest n entry v id.
    lookup_scopes n pre = NONE /\ FLOOKUP sc n = SOME entry /\ id <> n ==>
    lookup_scopes id (pre ++ (sc |+ (n, entry with <|value := v; popped := ps|>))::rest) =
    lookup_scopes id (pre ++ sc::rest)
Proof
  Induct >> simp[lookup_scopes_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP h id` >> gvs[] >>
  Cases_on `FLOOKUP h n` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem env_scopes_consistent_update_existing_value:
  env_scopes_consistent env cx (st with scopes := pre ++ sc::rest) /\
  lookup_scopes n pre = NONE /\ FLOOKUP sc n = SOME entry ==>
  env_scopes_consistent env cx
    (st with scopes := pre ++ (sc |+ (n, entry with <|value := v; popped := ps|>))::rest)
Proof
  rw[env_scopes_consistent_def]
  >- (
    Cases_on `id = n`
    >- (drule_all lookup_scopes_update_existing_value_at_found_scope >> simp[]) >>
    first_x_assum drule >> strip_tac >>
    drule_all lookup_scopes_update_existing_value_other >> simp[])
  >- (
    Cases_on `id = n`
    >- (drule_all lookup_scopes_update_existing_value_at_found_scope >> simp[] >> metis_tac[]) >>
    drule_all lookup_scopes_update_existing_value_other >> simp[] >> metis_tac[])
  >- (
    Cases_on `id = n`
    >- (
      drule_all lookup_scopes_update_existing_value_at_found_scope >> strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`id`, `ty`, `entry`] mp_tac) >> simp[]) >>
    drule_all lookup_scopes_update_existing_value_other >> strip_tac >> gvs[] >>
    first_x_assum drule_all >> simp[])
  >- (
    first_x_assum drule >> strip_tac >>
    Cases_on `id = n`
    >- (
      drule_all lookup_scopes_update_existing_value_at_found_scope >> strip_tac >> gvs[] >>
      qexists_tac `entry with <|value := v; popped := ps|>` >> gvs[]) >>
    drule_all lookup_scopes_update_existing_value_other >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[])
QED

Theorem env_consistent_update_existing_scope_value:
  env_consistent env cx (st with scopes := pre ++ sc::rest) /\
  lookup_scopes n pre = NONE /\ FLOOKUP sc n = SOME entry ==>
  env_consistent env cx
    (st with scopes := pre ++ (sc |+ (n, entry with <|value := v; popped := ps|>))::rest)
Proof
  simp[env_consistent_def] >>
  strip_tac >>
  reverse conj_tac >- (
    gvs[env_immutables_consistent_def] >>
    conj_tac >- metis_tac[] >>
    rpt gen_tac >> strip_tac >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    metis_tac[] ) >>
  funpow 2 drule_then drule env_scopes_consistent_update_existing_value >>
  simp[]
QED


Theorem update_name_preserves_state_well_typed:
  state_well_typed st /\ lookup_scopes id st.scopes = SOME entry /\
  value_has_type entry.type v ==>
  state_well_typed (update_name st id v)
Proof
  rw[update_name_def] >>
  Cases_on `find_containing_scope id st.scopes` >> gvs[]
  >- (drule find_containing_scope_none_lookup_scopes_none >> gvs[]) >>
  PairCases_on `x` >>
  drule find_containing_scope_structure >> strip_tac >> gvs[] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  gvs[state_well_typed_def] >>
  `EVERY scope_well_typed x0 /\ scope_well_typed x1 /\ EVERY scope_well_typed x3` by
    gvs[EVERY_APPEND] >>
  simp[EVERY_APPEND] >>
  irule scope_well_typed_update_value >> simp[]
QED

Theorem replace_operation_runtime_typed_value:
  assign_operation_runtime_typed env ty (Replace v) /\
  evaluate_type env.type_defs ty = SOME tv ==>
  value_has_type tv v
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >> gvs[]
QED

Theorem append_operation_runtime_typed_value:
  assign_operation_runtime_typed env ty (AppendOp v) /\ ty = ArrayT elem_ty bd /\
  evaluate_type env.type_defs elem_ty = SOME elem_tv ==>
  value_has_type elem_tv v
Proof
  rw[assign_operation_runtime_typed_def] >> gvs[]
QED

Theorem append_operation_runtime_typed_ArrayTV_value[local]:
  assign_operation_runtime_typed env ty (AppendOp v) ==>
  evaluate_type env.type_defs ty = SOME (ArrayTV app_elem_tv (Dynamic n)) ==>
  value_has_type app_elem_tv v
Proof
  rpt strip_tac >>
  fs[assign_operation_runtime_typed_def] >>
  gvs[] >>
  drule evaluate_type_ArrayT_cases >>
  simp[] >> strip_tac >>
  gvs[type_value_11, bound_11, optionTheory.SOME_11]
QED

Theorem pop_operation_runtime_typed_ArrayTV_exists[local]:
  assign_operation_runtime_typed env ty PopOp ==>
  evaluate_type env.type_defs ty = SOME (ArrayTV pop_elem_tv (Dynamic n)) ==>
  ?elem_ty. evaluate_type env.type_defs elem_ty = SOME pop_elem_tv ==>
  ty = ArrayT elem_ty (Dynamic n)
Proof
  rpt strip_tac >>
  fs[assign_operation_runtime_typed_def] >>
  gvs[] >>
  drule evaluate_type_ArrayT_cases >>
  simp[] >> strip_tac >>
  metis_tac[type_value_11, bound_11, optionTheory.SOME_11]
QED

Theorem place_leaf_path_typed_evaluate_type:
  place_leaf_path_typed env vt path ty final_tv ==> evaluate_type env.type_defs ty = SOME final_tv
Proof
  MAP_EVERY qid_spec_tac [`vt`, `path`] >>
  Induct_on `path` >> Cases_on `vt` >>
  rw[place_leaf_path_typed_def] >> gvs[] >>
  metis_tac[]
QED

Theorem place_leaf_typed_evaluate_type:
  place_leaf_typed env vt sbs ty final_tv ==> evaluate_type env.type_defs ty = SOME final_tv
Proof
  rw[place_leaf_typed_def] >>
  drule place_leaf_path_typed_evaluate_type >> simp[]
QED


Theorem evaluate_subscripts_leaf_well_typed:
  !subs tv a v.
    evaluate_subscripts tv a subs = INL v /\
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV ==>
    value_has_type (leaf_type tv subs) v /\
    well_formed_type_value (leaf_type tv subs)
Proof
  Induct >> simp[evaluate_subscripts_def, leaf_type_def] >>
  gen_tac >> Cases_on `h` >>
  simp[evaluate_subscripts_def, leaf_type_def] >>
  rpt gen_tac >> strip_tac
  >- (
    Cases_on `v` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
    Cases_on `tv` >> gvs[leaf_type_def, value_has_type_def, well_formed_type_value_def] >>
    drule array_index_has_type >> simp[] >> strip_tac >>
    first_x_assum drule_all >> simp[]) >>
  Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  Cases_on `tv` >>
  gvs[evaluate_subscripts_def, leaf_type_def, AllCaseEqs(), value_has_type_def] >>
  rename1 `StructTV ftypes` >>
  Cases_on `ALOOKUP ftypes s` >> gvs[] >>
  rename1 `ALOOKUP ftypes s = SOME ftv` >>
  `value_has_type ftv v'` by
    (drule struct_field_has_type >> disch_then drule >> strip_tac >> gvs[]) >>
  `well_formed_type_value ftv` by
    (gvs[well_formed_type_value_def, EVERY_MEM, MEM_MAP] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >>
     first_x_assum (qspec_then `(s, ftv)` mp_tac) >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem popped_value_well_typed:
  !arr v elem_tv n.
    popped_value arr = INL v /\
    value_has_type (ArrayTV elem_tv (Dynamic n)) arr ==>
    value_has_type elem_tv v
Proof
  Cases >> simp[popped_value_def, value_has_type_def] >>
  Cases_on `a` >> simp[popped_value_def, value_has_type_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MEM (LAST l) l` by (irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  gvs[all_have_type_EVERY, EVERY_MEM]
QED


Theorem env_consistent_record_update_same_scopes:
  env_consistent env cx st /\ st.scopes = scopes ==>
  env_consistent env cx (st with scopes := scopes)
Proof
  strip_tac >>
  `st with scopes := scopes = st` by gvs[evaluation_state_component_equality] >>
  gvs[]
QED

Theorem assign_operation_leaf_type_replace:
  evaluate_type env.type_defs ty = SOME leaf_tv /\
  assign_operation_runtime_typed env ty (Replace v) ==>
  value_has_type leaf_tv v
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >> gvs[]
QED

Theorem assign_operation_leaf_type_append:
  evaluate_type env.type_defs ty = SOME leaf_tv /\
  assign_operation_runtime_typed env ty (AppendOp v) ==>
  ?elem_tv n. leaf_tv = ArrayTV elem_tv (Dynamic n) /\ value_has_type elem_tv v
Proof
  rw[assign_operation_runtime_typed_def] >> gvs[evaluate_type_def]
QED


Theorem assign_operation_leaf_replace:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (Replace v) ==>
  value_has_type final_tv v
Proof
  metis_tac[assign_operation_leaf_type_replace, place_leaf_typed_evaluate_type]
QED

Theorem assign_operation_leaf_append:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (AppendOp v) ==>
  ?elem_tv n. final_tv = ArrayTV elem_tv (Dynamic n) /\ value_has_type elem_tv v
Proof
  metis_tac[assign_operation_leaf_type_append, place_leaf_typed_evaluate_type]
QED



Theorem set_storage_preserves_state_well_typed:
  state_well_typed st ==> state_well_typed (set_storage cx st is_trans storage')
Proof
  rw[state_well_typed_def]
QED

Theorem set_storage_preserves_accounts_well_typed:
  accounts_well_typed st.accounts ==>
  accounts_well_typed (set_storage cx st is_trans storage').accounts
Proof
  Cases_on `is_trans` >>
  simp[set_storage_def, accounts_well_typed_def, account_well_typed_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
       EQ_SYM_EQ] >>
  rpt strip_tac >> Cases_on `addr = cx.txn.target` >> simp[]
QED

Theorem write_storage_preserves_state_well_typed:
  state_well_typed st /\ accounts_well_typed st.accounts /\ value_has_type tv v /\
  write_storage_slot cx is_transient slot tv v st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  Cases_on `encode_value tv v` >> gvs[write_storage_slot_eq]
  >- (irule set_storage_preserves_state_well_typed >> simp[]) >>
  irule set_storage_preserves_accounts_well_typed >> simp[]
QED

Theorem write_storage_slot_preserves_state_well_typed_any:
  !cx is_transient slot tv v st res st'.
  write_storage_slot cx is_transient slot tv v st = (res, st') /\
  state_well_typed st ==> state_well_typed st'
Proof
  rpt strip_tac >>
  Cases_on `encode_value tv v` >> gvs[write_storage_slot_eq] >>
  irule set_storage_preserves_state_well_typed >> simp[]
QED

Theorem write_storage_slot_preserves_accounts_well_typed:
  !cx is_transient slot tv v st res st'.
  write_storage_slot cx is_transient slot tv v st = (res, st') /\
  accounts_well_typed st.accounts ==>
  accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  Cases_on `encode_value tv v` >> gvs[write_storage_slot_eq] >>
  irule set_storage_preserves_accounts_well_typed >> simp[]
QED

Theorem set_global_preserves_state_well_typed:
  !cx src n v st res st' env.
  set_global cx src n v st = (res, st') /\
  state_well_typed st /\ env_consistent env cx st ==>
  state_well_typed st'
Proof
  rpt strip_tac >>
  imp_res_tac set_global_scopes >>
  imp_res_tac set_global_immutables >>
  gvs[state_well_typed_def, env_consistent_def] >>
  metis_tac[]
QED

Theorem set_global_preserves_accounts_well_typed:
  !cx src n v st res st'.
  set_global cx src n v st = (res, st') /\ accounts_well_typed st.accounts ==>
  accounts_well_typed st'.accounts
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_name n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src x'1` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >> gvs[return_def, raise_def] >>
  drule_all write_storage_slot_preserves_accounts_well_typed >> simp[]
QED

Theorem resolve_array_element_preserves_accounts_well_typed:
  resolve_array_element cx b slot tv subs st = (res, st') /\
  accounts_well_typed st.accounts ==>
  accounts_well_typed st'.accounts
Proof
  rpt strip_tac >> imp_res_tac resolve_array_element_state >> gvs[]
QED

Theorem write_storage_slot_preserves_env_consistent:
  write_storage_slot cx is_transient slot tv v st = (res, st') /\
  env_consistent env cx st ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >>
  Cases_on `encode_value tv v` >>
  gvs[write_storage_slot_eq, set_storage_def, env_consistent_def,
      env_scopes_consistent_def, env_immutables_consistent_def] >>
  rw[] >> metis_tac[]
QED

Theorem set_global_preserves_env_consistent:
  set_global cx src n v st = (res, st') /\ env_consistent env cx st ==>
  env_consistent env cx st'
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_name n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `lookup_var_slot_from_layout cx b src x'1` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >> gvs[return_def, raise_def] >>
  drule_all write_storage_slot_preserves_env_consistent >> simp[]
QED

Theorem resolve_array_element_preserves_env_consistent:
  resolve_array_element cx b slot tv subs st = (res, st') /\ env_consistent env cx st ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >> imp_res_tac resolve_array_element_state >> gvs[]
QED

Theorem read_storage_slot_preserves_env_consistent:
  read_storage_slot cx is_transient slot tv st = (res, st') /\ env_consistent env cx st ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >> imp_res_tac read_storage_slot_state >> gvs[]
QED

Theorem get_storage_backend_preserves_env_consistent:
  get_storage_backend cx is_transient st = (res, st') /\ env_consistent env cx st ==>
  env_consistent env cx st'
Proof
  rpt strip_tac >> imp_res_tac get_storage_backend_state >> gvs[]
QED

Theorem imms_well_typed_set_source_immutables_update:
  imms_well_typed imms /\
  value_has_type tv v /\ well_formed_type_value tv ==>
  imms_well_typed (set_source_immutables src (get_source_immutables src imms |+ (n,(tv,v))) imms)
Proof
  rw[imms_well_typed_def, set_source_immutables_def, get_source_immutables_def] >>
  gvs[alistTheory.ALOOKUP_def, FLOOKUP_UPDATE, alistTheory.ALOOKUP_ADELKEY, AllCaseEqs()] >>
  Cases_on `src_id_opt = src` >> gvs[]
  >- (
    Cases_on `id = n` >> gvs[FLOOKUP_UPDATE] >>
    qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
    Cases_on `ALOOKUP imms src` >> gvs[] >> metis_tac[]) >>
  Cases_on `id = n` >> gvs[FLOOKUP_UPDATE] >>
  qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
  Cases_on `ALOOKUP imms src` >> gvs[] >> metis_tac[]
QED

Theorem get_source_set_source_immutables_same[simp]:
  get_source_immutables s (set_source_immutables s imms blah) = imms
Proof
  rw[set_source_immutables_def] >>
  rw[get_source_immutables_def]
QED

Theorem get_source_set_source_immutables:
  get_source_immutables s1 (set_source_immutables s2 blah rest) =
  if s1 = s2 then blah else get_source_immutables s1 rest
Proof
  rw[] >>
  gvs[set_source_immutables_def, get_source_immutables_def] >>
  simp[alistTheory.ALOOKUP_ADELKEY]
QED

Theorem set_immutable_preserves_env_consistent:
  env_consistent env cx st /\
  FLOOKUP env.bare_globals (src,n) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  set_immutable cx src n tv v st = (res, st') ==>
  env_consistent env cx st'
Proof
  rw[set_immutable_def, get_address_immutables_def, bind_def,
     lift_option_type_def, lift_option_def, set_address_immutables_def,
     return_def, raise_def, AllCaseEqs(), LET_THM] >>
  qpat_x_assum `(case ALOOKUP _ _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `ALOOKUP _ _ = SOME _` assume_tac >>
  gvs[env_consistent_def] >>
  conj_tac >- (gvs[env_scopes_consistent_def] >> metis_tac[] ) >>
  gvs[env_immutables_consistent_def, FLOOKUP_UPDATE] >>
  conj_tac >- (
    rw[get_source_set_source_immutables, FLOOKUP_UPDATE] >>
    Cases_on `n = id` >> gvs[] >> metis_tac[]) >>
  conj_tac >- (
    rw[get_source_set_source_immutables, FLOOKUP_UPDATE] >>
    Cases_on `n = id` >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  rpt gen_tac >>
  reverse(simp[get_source_set_source_immutables] >>
          rw[FLOOKUP_UPDATE]) >- metis_tac[] >>
  reverse(pop_assum mp_tac >> rw[] >> gvs[]) >- metis_tac[] >>
  first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM) >>
  `env.type_defs = get_tenv cx` by gvs[env_context_consistent_def] >>
  gvs[env_context_consistent_def] >>
  last_x_assum drule_all >>
  strip_tac >> gvs[]
QED

Theorem set_immutable_preserves_state_well_typed:
  state_well_typed st /\ value_has_type tv v /\ well_formed_type_value tv /\
  set_immutable cx src n tv v st = (res, st') ==>
  state_well_typed st'
Proof
  rw[set_immutable_def, get_address_immutables_def, bind_def,
     lift_option_type_def, lift_option_def, set_address_immutables_def,
     return_def, raise_def, AllCaseEqs(), LET_THM] >>
  qpat_x_assum `(case ALOOKUP _ _ of _ => _) _ = _` mp_tac >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  gvs[state_well_typed_def] >>
  conj_tac
  >- (
    `imms_well_typed imms` by (
      fs[EVERY_MEM, FORALL_PROD] >> first_x_assum irule >>
      imp_res_tac alistTheory.ALOOKUP_MEM >> goal_assum drule) >>
    irule imms_well_typed_set_source_immutables_update >> simp[]) >>
  gvs[EVERY_MEM, FORALL_PROD, alistTheory.ADELKEY_def, MEM_FILTER] >>
  rpt strip_tac >> first_x_assum irule >> goal_assum drule
QED

Definition LIST_REL3_def:
  LIST_REL3 R [] [] [] = T /\
  LIST_REL3 R (x::xs) (y::ys) (z::zs) = (R x y z /\ LIST_REL3 R xs ys zs) /\
  LIST_REL3 R _ _ _ = F
End


Theorem LIST_REL3_LENGTHS:
  !R xs ys zs. LIST_REL3 R xs ys zs ==> LENGTH xs = LENGTH ys /\ LENGTH ys = LENGTH zs
Proof
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >>
  simp[LIST_REL3_def] >> metis_tac[]
QED

Theorem LIST_REL3_EL:
  !R xs ys zs n.
    LIST_REL3 R xs ys zs /\ n < LENGTH xs ==>
    R (EL n xs) (EL n ys) (EL n zs)
Proof
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >>
  simp[LIST_REL3_def] >> rw[] >> Cases_on `n` >> gvs[]
QED

Theorem LIST_REL3_from_LIST_REL2:
  !R xs ys zs. LIST_REL (\x (y,z). R x y z) xs (ZIP (ys,zs)) /\
                LENGTH ys = LENGTH zs /\ LENGTH xs = LENGTH ys ==>
                LIST_REL3 R xs ys zs
Proof
  Induct_on `xs` >> Cases_on `ys` >> Cases_on `zs` >>
  simp[LIST_REL3_def]
QED


Theorem read_storage_slot_well_typed_value:
  read_storage_slot cx is_transient slot tv st = (INL v, st') /\
  well_formed_type_value tv ==>
  value_has_type tv v
Proof
  simp[read_storage_slot_def, bind_def, AllCaseEqs(),
       get_storage_backend_def, return_def, lift_option_def,
       option_CASE_rator, raise_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all (cj 1 decode_value_well_typed) >> simp[]
QED


Theorem find_containing_scope_preserved_under_preserves_tv[local]:
  preserves_tv cx st st' ==>
  MAP FDOM st'.scopes = MAP FDOM st.scopes ==>
  find_containing_scope id st.scopes = SOME (pre, env, entry, rest) ==>
  ?pre' env' entry' rest'.
    find_containing_scope id st'.scopes = SOME (pre', env', entry', rest')
Proof
  rpt strip_tac >>
  `lookup_scopes id st.scopes = SOME entry` by metis_tac[find_containing_scope_lookup] >>
  `IS_SOME (lookup_scopes id st'.scopes)` by metis_tac[lookup_scopes_same_fdoms_some] >>
  Cases_on `lookup_scopes id st'.scopes` >> gvs[] >>
  metis_tac[lookup_scopes_find_containing_scope]
QED

Theorem find_containing_scope_assignable_of_preserved[local]:
  !pre' env' entry' rest'.
    preserves_tv cx st st' ==>
    MAP FDOM st'.scopes = MAP FDOM st.scopes ==>
    find_containing_scope id st.scopes = SOME (pre, env, entry, rest) ==>
    entry.assignable ==>
    find_containing_scope id st'.scopes = SOME (pre', env', entry', rest') ==>
    entry'.assignable
Proof
  rpt strip_tac >>
  `lookup_scopes id st.scopes = SOME entry` by metis_tac[find_containing_scope_lookup] >>
  drule_all lookup_scopes_assignable_preserved_under_preserves_tv >> strip_tac >>
  `lookup_scopes id st'.scopes = SOME entry'` by metis_tac[find_containing_scope_lookup] >>
  metis_tac[SOME_11]
QED


Theorem lookup_global_success_get_module_code:
  lookup_global cx src n st = (INL tv, st') ==> ?code. get_module_code cx src = SOME code
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, raise_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def]
QED

Theorem top_level_Type_storage_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type base_ty) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name n ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
  typ = base_ty
Proof
  rw[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem top_level_Type_not_hashmap_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type base_ty) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name n ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
  F
Proof
  rw[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem top_level_HashMap_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (HashMapT kt vt) /\
  get_module_code cx src = SOME ts ==>
  ?is_transient id_str.
    find_var_decl_by_name n ts = SOME (HashMapVarDecl is_transient kt vt,id_str)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `(!src id kt vt. FLOOKUP _ _ = SOME (HashMapT kt vt) ==> _)` drule >>
  rw[] >>
  rename1 `find_var_decl_by_name n ts =
    SOME (HashMapVarDecl transient kt vt,decl_name)` >>
  qexistsl_tac [`transient`, `decl_name`] >> simp[]
QED

Theorem top_level_vtype_well_formed:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME vt ==>
  well_formed_vtype env.type_defs vt
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  metis_tac[]
QED


Theorem lookup_global_Value_not_HashMapVarDecl:
  lookup_global cx src n st = (INL (Value v), st') /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_name n code = SOME p /\
  FST p = HashMapVarDecl is_t kt vt ==>
  F
Proof
  rpt strip_tac >> Cases_on `p` >> gvs[] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, raise_def,
       return_def, AllCaseEqs()] >>
  Cases_on `lookup_var_slot_from_layout cx is_t src r` >>
  simp[return_def, raise_def, bind_def]
QED


Theorem lookup_global_HashMapRef_not_StorageVarDecl:
  lookup_global cx src n st = (INL (HashMapRef is_t bs kt vt), st') ==>
  get_module_code cx src = SOME code ==>
  find_var_decl_by_name n code = SOME (StorageVarDecl is_transient' typ, id) ==>
  F
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, eval_result_CASE_rator, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED


Theorem lookup_global_HashMapRef:
  lookup_global cx src n st = (INL (HashMapRef is_t bs kt vt), st') ==>
  ?code id_str.
    get_module_code cx src = SOME code /\
    find_var_decl_by_name n code = SOME (HashMapVarDecl is_t kt vt, id_str)
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, eval_result_CASE_rator, LET_THM, AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[] >> rpt strip_tac >> gvs[]
QED


(* Canonical storage lookup resolves a place; loading is a separate guarantee. *)
Theorem lookup_global_storage_Value_typed:
  lookup_global cx src n st = (INL pv, st') /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_name n code = SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  pv = PlaceR (StoragePlace is_transient (n2w slot) tv) /\
  !v final. read_result cx pv st' = (INL v,final) ==> value_has_type tv v
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  strip_tac >> gvs[read_result_def, read_place_def] >>
  metis_tac[read_storage_slot_success_type, evaluate_type_well_formed_type_value,
            value_has_type_NoneTV]
QED

Theorem write_storage_slot_no_type_error_from_value_has_type:
  value_has_type tv v ==>
  write_storage_slot cx is_transient slot tv v st <>
    (INR (Error (TypeError msg)), st')
Proof
  rw[] >>
  `IS_SOME (encode_value tv v)` by metis_tac[value_has_type_equiv] >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  CCONTR_TAC >> gvs[] >>
  Cases_on `is_transient` >>
  gvs[write_storage_slot_def, bind_def, lift_option_def,
      get_storage_backend_def, get_transient_storage_def, get_accounts_def,
      return_def, raise_def, set_storage_backend_def, update_transient_def,
      update_accounts_def]
QED

Theorem set_global_storage_no_type_error:
  get_module_code cx src = SOME code /\
  find_var_decl_by_name n code = SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v ==>
  set_global cx src n v st <> (INR (Error (TypeError msg)), st')
Proof
  rw[set_global_def, bind_def, lift_option_type_def, raise_def, return_def,
     AllCaseEqs(), option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator] >>
  drule_all write_storage_slot_no_type_error_from_value_has_type >> simp[]
QED

Theorem assign_subscripts_preserves_type_runtime_typed:
  assign_subscripts tv old_v subs op = INL new_v /\
  value_has_type tv old_v /\
  well_formed_type_value tv /\
  evaluate_type env.type_defs ty = SOME (leaf_type tv subs) /\
  assign_operation_runtime_typed env ty op ==>
  value_has_type tv new_v
Proof
  rpt strip_tac >>
  qspecl_then [`tv`,`old_v`,`subs`,`op`,`new_v`]
    mp_tac assign_subscripts_preserves_type >>
  simp[] >>
  impl_tac >- (
    rpt strip_tac >> gvs[]
    >- metis_tac[assign_operation_leaf_type_replace] >>
    metis_tac[assign_operation_leaf_type_append]) >>
  simp[]
QED

Theorem top_level_vtype_Type_storage_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type root_ty) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_name n code = SOME (StorageVarDecl is_transient typ,id_str) ==>
  typ = root_ty
Proof
  strip_tac >>
  gvs[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def] >>
  first_x_assum $ drule_then drule >>
  strip_tac >>
  qpat_x_assum `!is_transient typ id_str. _`
    (qspecl_then [`is_transient`, `typ`, `id_str`] mp_tac) >>
  simp[]
QED


Theorem assign_subscripts_replace_leaf_no_type_error:
  assign_subscripts tv leaf [] (Replace nv) <> INR (TypeError msg)
Proof
  simp[Once assign_subscripts_def]
QED

Theorem append_element_no_type_error:
  value_has_type (ArrayTV elem_tv (Dynamic n)) arr_v /\
  value_has_type elem_tv new_elem ==>
  append_element (ArrayTV elem_tv (Dynamic n)) arr_v new_elem <> INR (TypeError msg)
Proof
  Cases_on `arr_v` >> simp[value_has_type_def, append_element_def] >>
  Cases_on `a` >> simp[value_has_type_def, append_element_def] >>
  rw[] >> gvs[] >>
  drule safe_cast_well_typed >> simp[]
QED

Theorem assign_subscripts_append_leaf_no_type_error:
  value_has_type (ArrayTV elem_tv (Dynamic n)) leaf /\
  value_has_type elem_tv nv ==>
  assign_subscripts (ArrayTV elem_tv (Dynamic n)) leaf [] (AppendOp nv) <>
    INR (TypeError msg)
Proof
  simp[Once assign_subscripts_def] >>
  metis_tac[append_element_no_type_error]
QED

Theorem pop_element_no_type_error:
  value_has_type (ArrayTV elem_tv (Dynamic n)) arr_v ==>
  pop_element arr_v <> INR (TypeError msg)
Proof
  Cases_on `arr_v` >> simp[value_has_type_def, pop_element_def] >>
  Cases_on `a` >> simp[value_has_type_def, pop_element_def]
QED

Theorem assign_subscripts_pop_leaf_no_type_error:
  value_has_type (ArrayTV elem_tv (Dynamic n)) leaf ==>
  assign_subscripts (ArrayTV elem_tv (Dynamic n)) leaf [] PopOp <>
    INR (TypeError msg)
Proof
  simp[Once assign_subscripts_def] >>
  metis_tac[pop_element_no_type_error]
QED

Theorem int_typed_value_is_IntV:
  is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?i. v = IntV i
Proof
  Cases_on `ty` >> rw[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem numeric_typed_value_is_numeric:
  is_numeric_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  (?i. v = IntV i) \/ (?d. v = DecimalV d)
Proof
  rw[is_numeric_type_def] >-
    (drule_all int_typed_value_is_IntV >> simp[]) >>
  Cases_on `v` >> gvs[evaluate_type_def, value_has_type_def]
QED

Theorem bool_typed_value_is_BoolV:
  is_bool_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?b. v = BoolV b
Proof
  Cases_on `ty` >> gvs[is_bool_type_def, evaluate_type_def] >>
  Cases_on `b` >> gvs[is_bool_type_def, evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem flag_typed_value_is_FlagV:
  is_flag_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  ?n. v = FlagV n
Proof
  Cases_on `ty` >> rw[is_flag_type_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem well_typed_update_binop_no_type_error:
  well_typed_binop lhs_ty bop lhs_ty rhs_ty /\
  evaluate_type tenv lhs_ty = SOME lhs_tv /\
  evaluate_type tenv rhs_ty = SOME rhs_tv /\
  value_has_type lhs_tv lhs /\
  value_has_type rhs_tv rhs /\
  u = (case type_to_int_bound lhs_ty of NONE => Unsigned 0 | SOME u => u) ==>
  evaluate_binop u lhs_tv bop lhs rhs <> INR (TypeError msg)
Proof
  (* TODO(proof-cleanup): this could be proved directly by binop-family
     inversion.  For now it is the assignment-shaped instance of the existing
     builtin no-TypeError theorem. *)
  metis_tac[well_typed_binop_no_type_error]
QED


Theorem struct_has_type_alookup_none:
  !l al id. struct_has_type l al /\ ALOOKUP al id = NONE ==> ALOOKUP l id = NONE
Proof
  Induct >> Cases_on `al` >> simp[value_has_type_def] >>
  Cases >> Cases_on `h` >> simp[value_has_type_def] >> rw[] >> gvs[] >>
  Cases_on `id = q` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem array_set_index_no_type_error:
  array_index (ArrayTV elem_tv bd) av i = SOME old /\
  value_has_type (ArrayTV elem_tv bd) (ArrayV av) ==>
  array_set_index (ArrayTV elem_tv bd) av i v <> INR (TypeError msg)
Proof
  Cases_on `0 <= i` >> gvs[array_index_def, array_set_index_def, LET_THM] >>
  Cases_on `av` >> gvs[value_has_type_def, array_set_index_def, array_index_def] >>
  Cases_on `bd` >> gvs[value_has_type_def, array_set_index_def, array_index_def, AllCaseEqs()]
QED

Theorem assign_operation_runtime_typed_leaf_no_type_error:
  !env leaf_ty op leaf_tv leaf msg.
    assign_operation_runtime_typed env leaf_ty op /\
    evaluate_type env.type_defs leaf_ty = SOME leaf_tv /\
    value_has_type leaf_tv leaf ==>
    assign_subscripts leaf_tv leaf [] op <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `op` >- (
    gvs[assign_operation_runtime_typed_def, value_runtime_typed_def, Once assign_subscripts_def]) >- (
    rename1 `AppendOp v` >>
    gvs[assign_operation_runtime_typed_def, evaluate_type_def] >>
    drule_all assign_subscripts_append_leaf_no_type_error >> simp[]) >>
  gvs[assign_operation_runtime_typed_def, evaluate_type_def] >>
  drule_all assign_subscripts_pop_leaf_no_type_error >> simp[]
QED

Theorem assign_subscripts_no_type_error_from_leaf:
  !tv a subs op.
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV /\
    (!leaf msg.
       value_has_type (leaf_type tv subs) leaf ==>
       assign_subscripts (leaf_type tv subs) leaf [] op <>
         INR (TypeError msg)) ==>
    !msg. assign_subscripts tv a subs op <> INR (TypeError msg)
Proof
  Induct_on `subs` >- (
    simp[leaf_type_def] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
    first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >> gvs[leaf_type_def] >- (
    Cases_on `v` >> gvs[Once assign_subscripts_def, leaf_type_def] >>
    Cases_on `a` >> gvs[Once assign_subscripts_def] >>
    Cases_on `tv` >> gvs[value_has_type_def, well_formed_type_value_def, leaf_type_def] >>
    Cases_on `array_index (ArrayTV t b) a' i` >> gvs[] >>
    `value_has_type t x` by (
      irule array_index_has_type >> simp[] >>
      goal_assum drule >> simp[]) >>
    qpat_x_assum `!tv a op. _` (qspecl_then [`t`,`x`,`op`] mp_tac) >>
    impl_tac >- (
      simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
    strip_tac >>
    Cases_on `assign_subscripts t x subs op` >> gvs[] >> rpt strip_tac >>
    `array_set_index (ArrayTV t b) a' i x' <> INR (TypeError msg)` by (
      irule array_set_index_no_type_error >> simp[] >>
      goal_assum drule >> simp[]) >>
    gvs[]) >>
  Cases_on `a` >> gvs[Once assign_subscripts_def] >>
  Cases_on `tv` >> gvs[value_has_type_def, well_formed_type_value_def, leaf_type_def] >>
  reverse (Cases_on `ALOOKUP l s`) >> gvs[] >- (
    rename1 `ALOOKUP l s = SOME fv` >>
    `?(field_ty:type_value). ALOOKUP l' s = SOME field_ty /\ value_has_type field_ty fv` by
      (drule_all struct_field_has_type >> simp[]) >>
    gvs[] >>
    `well_formed_type_value field_ty` by
      (gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
       drule alistTheory.ALOOKUP_MEM >> strip_tac >>
       first_x_assum irule >> metis_tac[]) >>
    first_x_assum (qspecl_then [`field_ty`,`fv`,`op`] mp_tac) >>
    impl_tac >- (
      simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
    strip_tac >>
    Cases_on `assign_subscripts field_ty fv subs op` >> gvs[]) >>
  drule_all struct_has_type_alookup_none >> strip_tac >> gvs[]
QED

Theorem assign_subscripts_no_type_error_runtime_typed:
  !tv a subs op env leaf_ty msg.
    value_has_type tv a /\
    well_formed_type_value tv /\
    leaf_type tv subs <> NoneTV /\
    assign_operation_runtime_typed env leaf_ty op /\
    evaluate_type env.type_defs leaf_ty = SOME (leaf_type tv subs) ==>
    assign_subscripts tv a subs op <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  qspecl_then [`tv`,`a`,`subs`,`op`] mp_tac assign_subscripts_no_type_error_from_leaf >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    drule_all assign_operation_runtime_typed_leaf_no_type_error >> simp[]) >>
  strip_tac >> first_x_assum (qspec_then `msg` mp_tac) >> simp[]
QED


Theorem option_neq_none_imp_is_some:
  !x. x ≠ NONE ⇔ IS_SOME x
Proof
  Cases_on `x` >> simp[optionTheory.IS_SOME_DEF]
QED

Theorem well_formed_vtype_split_hashmap_subscripts_well_formed_type:
  !tenv vt subs final_type kts remaining.
    well_formed_vtype tenv vt ==>
    split_hashmap_subscripts vt subs = SOME (final_type, kts, remaining) ==>
    well_formed_type tenv final_type
Proof
  Induct_on `vt` >> rw[split_hashmap_subscripts_def] >-
  gvs[well_formed_vtype_def] >>
  Cases_on `subs` >> gvs[split_hashmap_subscripts_def] >>
  gvs[well_formed_vtype_def] >>
  Cases_on `split_hashmap_subscripts vt t'` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  first_x_assum drule >>
  disch_then (qspecl_then [`t'`, `final_type`, `x1`, `remaining`] mp_tac) >>
  impl_tac >- (simp[]) >>
  strip_tac >> gvs[well_formed_vtype_def]
QED

Theorem compute_hashmap_slot_subscripts_to_values:
  !slot kts ks.
    LENGTH kts = LENGTH ks ==>
    EVERY ((<>) NONE o subscript_to_value) ks ==>
    compute_hashmap_slot slot kts ks <> NONE
Proof
  Induct_on `kts` >> Cases_on `ks` >> rw[] >>
  gvs[compute_hashmap_slot_def] >>
  Cases_on `subscript_to_value h` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem split_hashmap_subscripts_some_imp:
  !vt subs final_type kts remaining.
    split_hashmap_subscripts vt subs = SOME (final_type, kts, remaining) ==>
    LENGTH kts + LENGTH remaining = LENGTH subs
Proof
  gen_tac >> Induct_on `vt` >- rw[split_hashmap_subscripts_def] >>
  rw[split_hashmap_subscripts_def] >>
  Cases_on `subs` >> gvs[split_hashmap_subscripts_def] >>
  Cases_on `split_hashmap_subscripts vt t'` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  first_x_assum (qspecl_then [`t'`, `final_type`, `x1`, `remaining`] mp_tac) >>
  simp[]
QED

Theorem compute_hashmap_slot_prefix_some:
  !base_slot kt kts first_sub rest_subs remaining.
    LENGTH kts + LENGTH remaining = LENGTH rest_subs ==>
    EVERY ((<>) NONE o subscript_to_value)
      (first_sub :: TAKE (LENGTH kts) rest_subs) ==>
    compute_hashmap_slot base_slot (kt::kts)
      (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) <> NONE
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `LENGTH rest_subs - LENGTH remaining = LENGTH kts` by decide_tac >>
  `LENGTH rest_subs - LENGTH remaining <= LENGTH rest_subs` by decide_tac >>
  irule compute_hashmap_slot_subscripts_to_values >>
  conj_tac >- (
    `LENGTH (TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) = LENGTH rest_subs - LENGTH remaining` by
      metis_tac[LENGTH_TAKE_EQ] >>
    fs[LENGTH] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem target_path_step_type_HashMapT_ValueSubscript:
  !env kt vt sb next_vt.
    target_path_step_type env (HashMapT kt vt) sb next_vt ==>
    subscript_to_value sb <> NONE
Proof
  Cases_on `sb` >> rw[target_path_step_type_def, subscript_to_value_def]
QED

Theorem target_path_step_type_HashMapT_next_vt:
  !env kt vt sb next_vt.
    target_path_step_type env (HashMapT kt vt) sb next_vt ==>
    next_vt = vt
Proof
  Cases_on `sb` >> rw[target_path_step_type_def]
QED

Theorem target_path_type_HashMapT_not_nil:
  !env kt vt sbs ty.
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==> sbs <> []
Proof
  Cases_on `sbs` >> simp[target_path_type_def]
QED

Theorem place_leaf_path_typed_imp_split_hashmap_subscripts:
  !env vt path ty final_tv.
    place_leaf_path_typed env vt path ty final_tv ==>
    split_hashmap_subscripts vt path <> NONE
Proof
  ho_match_mp_tac place_leaf_path_typed_ind >> rw[] >>
  gvs[place_leaf_path_typed_def, split_hashmap_subscripts_def] >>
  Cases_on `split_hashmap_subscripts vt path` >> gvs[] >>
  PairCases_on `x` >> gvs[]
QED

Theorem target_path_type_HashMapT_last_step:
  !env kt vt sbs final_vt.
    target_path_type env (HashMapT kt vt) sbs final_vt ==>
    sbs <> [] ==>
    target_path_step_type env (HashMapT kt vt) (LAST sbs) vt
Proof
  Induct_on `sbs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[target_path_type_def] >>
  Cases_on `sbs` >> gvs[LAST_DEF] >-
    (gvs[target_path_type_def] >>
     drule target_path_step_type_HashMapT_next_vt >> rw[] >>
     fs[target_path_step_type_def]) >>
  first_x_assum drule >> disch_then irule >> simp[]
QED

Theorem target_path_type_HashMapT_front_path:
  !env kt vt sbs final_vt.
    target_path_type env (HashMapT kt vt) sbs final_vt ==>
    sbs <> [] ==>
    target_path_type env vt (FRONT sbs) final_vt
Proof
  Induct_on `sbs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[target_path_type_def] >>
  Cases_on `sbs` >> gvs[] >-
    (gvs[target_path_type_def] >>
     drule target_path_step_type_HashMapT_next_vt >> rw[]) >>
  first_x_assum (qspecl_then [`env`,`kt`,`vt`,`mid_vt`] mp_tac) >>
  simp[] >>
  metis_tac[target_path_type_def]
QED

Theorem SNOC_LAST_FRONT_eq:
  !l. l <> [] ==> (l = SNOC (LAST l) (FRONT l))
Proof
  Induct >- simp[] >>
  rpt strip_tac >>
  Cases_on `l` >> simp[]
QED

Theorem REVERSE_SNOC_eq:
  !x xs. REVERSE (SNOC x xs) = x :: REVERSE xs
Proof
  gen_tac >> Induct_on `xs` >> simp[]
QED

Theorem TL_REVERSE_SNOC:
  !x xs. TL (REVERSE (SNOC x xs)) = REVERSE xs
Proof
  simp[REVERSE_SNOC_eq]
QED

Theorem TL_REVERSE_eq_REVERSE_FRONT:
  !l. l <> [] ==> (TL (REVERSE l) = REVERSE (FRONT l))
Proof
  rpt strip_tac >>
  qsuff_tac `REVERSE l = LAST l :: REVERSE (FRONT l)` >- simp[] >>
  metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq]
QED

Theorem HD_REVERSE_EQ_LAST:
  !l. l <> [] ==> (HD (REVERSE l) = LAST l)
Proof
  rpt strip_tac >>
  qsuff_tac `REVERSE l = LAST l :: REVERSE (FRONT l)` >- simp[] >>
  metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq]
QED

Theorem REVERSE_CONS_IMP_LENGTH:
  !l h t. REVERSE l = h :: t ==> LENGTH l = SUC (LENGTH t)
Proof
  rpt strip_tac >>
  qsuff_tac `LENGTH l = LENGTH (h :: t)` >- simp[] >>
  metis_tac[LENGTH_REVERSE]
QED

Theorem target_path_type_HashMapT_hashmap_prefix_ValueSubscript:
  !env kt vt sbs ty final_type kts remaining.
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    split_hashmap_subscripts vt (TL (REVERSE sbs)) = SOME (final_type, kts, remaining) ==>
    EVERY ((<>) NONE o subscript_to_value)
      (LAST sbs :: TAKE (LENGTH kts) (TL (REVERSE sbs)))
Proof
  Induct_on `vt` >- (
  (* Base: vt = Type t, so split_hashmap_subscripts gives kts = [] *)
    rpt strip_tac >>
    gvs[split_hashmap_subscripts_def] >>
    `sbs <> []` by metis_tac[target_path_type_HashMapT_not_nil] >>
    drule target_path_type_HashMapT_last_step >> simp[] >> strip_tac >>
    metis_tac[target_path_step_type_HashMapT_ValueSubscript]) >>
  (* Step: vt = HashMapT t vt' *)
  rpt strip_tac >>
  `sbs <> []` by metis_tac[target_path_type_HashMapT_not_nil] >>
  `TL (REVERSE sbs) = REVERSE (FRONT sbs)` by
    metis_tac[TL_REVERSE_eq_REVERSE_FRONT] >>
  drule target_path_type_HashMapT_last_step >> simp[] >> strip_tac >>
  `subscript_to_value (LAST sbs) <> NONE` by
    metis_tac[target_path_step_type_HashMapT_ValueSubscript] >>
  `FRONT sbs <> []` by (
    CCONTR_TAC >> gvs[] >>
    Cases_on `REVERSE (FRONT sbs)` >> gvs[split_hashmap_subscripts_def]) >>
  `target_path_type env (HashMapT t vt) (FRONT sbs) (Type ty)` by (
    drule target_path_type_HashMapT_front_path >> simp[]) >>
  `subscript_to_value (LAST (FRONT sbs)) <> NONE` by
    metis_tac[target_path_type_HashMapT_last_step,
              target_path_step_type_HashMapT_ValueSubscript] >>
  `TL (REVERSE (FRONT sbs)) = REVERSE (FRONT (FRONT sbs))` by
    metis_tac[TL_REVERSE_eq_REVERSE_FRONT] >>
  (* Expand split_hashmap_subscripts (HashMapT t vt) ... using the def.
     We have: split_hashmap_subscripts (HashMapT t vt) (TL (REVERSE sbs)) = SOME (...)
     and: TL (REVERSE sbs) = REVERSE (FRONT sbs) and REVERSE (FRONT sbs) ≠ []
     So: split_hashmap_subscripts (HashMapT t vt) (REVERSE (FRONT sbs)) = SOME (...)
     By def: split_hashmap_subscripts (HashMapT t vt) (h::t') = case split_hashmap_subscripts vt t' of ...
     Cases_on the inner to resolve. *)
  `REVERSE (FRONT sbs) ≠ []` by simp[] >>
  (* Rewrite: replace TL (REVERSE sbs) with REVERSE (FRONT sbs) in assumption 2 *)
  `split_hashmap_subscripts (HashMapT t vt) (REVERSE (FRONT sbs)) = SOME (final_type, kts, remaining)` by (
    qpat_x_assum `split_hashmap_subscripts (HashMapT t vt) _ = SOME _` mp_tac >>
    simp[TL_REVERSE_eq_REVERSE_FRONT]) >>
  (* Now case-split on the inner recursive call *)
  Cases_on `split_hashmap_subscripts vt (REVERSE (FRONT (FRONT sbs)))` >-
    (* NONE case: by def, REVERSE (FRONT sbs) = h::t means outer = NONE (since inner = NONE).
       This contradicts assumption 12 saying it's SOME. *)
    (Cases_on `REVERSE (FRONT sbs)` >> gvs[split_hashmap_subscripts_def]) >>
  (* SOME case: derive components from the SOME result *)
  PairCases_on `x` >> gvs[split_hashmap_subscripts_def] >>
  (* Now: kts = t :: x1, final_type = x0, remaining = x2 *)
  (* split_hashmap_subscripts vt (REVERSE (FRONT (FRONT sbs))) = SOME (x0, x1, x2) *)
  (* Apply IH with sbs' = FRONT sbs.
     The IH needs: target_path_type env (HashMapT t vt) (FRONT sbs) (Type ty)
     and: split_hashmap_subscripts vt (TL (REVERSE (FRONT sbs))) = SOME (x0,x1,x2)
     Both are derivable from current assumptions. *)
  `split_hashmap_subscripts vt (TL (REVERSE (FRONT sbs))) = SOME (x0,x1,x2)` by (
    simp[TL_REVERSE_eq_REVERSE_FRONT]) >>
  first_x_assum (qspecl_then [
    `env`, `t`, `FRONT sbs`, `ty`,
    `x0`, `x1`, `x2`] drule_all) >>
  strip_tac >>
  (* Derive kts = t :: x1 from the split_hashmap_subscripts definition.
     From assumptions: split_hashmap_subscripts (HashMapT t vt) (REVERSE (FRONT sbs)) = SOME (final_type,kts,remaining)
     and: REVERSE (FRONT sbs) ≠ [], and split_hashmap_subscripts vt (TL ...) = SOME (x0,x1,x2)
     By def: result = SOME (x0, t::x1, x2), so kts = t :: x1. *)
  `kts = t :: x1` by (
    qpat_x_assum `split_hashmap_subscripts (HashMapT t vt) _ = SOME _` mp_tac >>
    simp[split_hashmap_subscripts_def] >>
    Cases_on `REVERSE (FRONT sbs)` >> gvs[split_hashmap_subscripts_def] >>
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  (* Now kts = t :: x1, so the goal EVERY ... (TAKE (LENGTH (t::x1)) (REVERSE (FRONT sbs)))
     = EVERY ... (TAKE (SUC (LENGTH x1)) (REVERSE (FRONT sbs))) *)
  `REVERSE (FRONT sbs) = LAST (FRONT sbs) :: REVERSE (FRONT (FRONT sbs))` by
    metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq] >>
  (* TAKE (SUC n) (h :: t) = h :: TAKE n t, and EVERY f (h :: t) = f h ∧ EVERY f t *)
  simp[] >>
  (* subscript_to_value (LAST (FRONT sbs)) ≠ NONE from assumption,
     and EVERY ... (TAKE (LENGTH x1) (REVERSE (FRONT (FRONT sbs)))) from IH
     after rewriting TL (REVERSE (FRONT sbs)) = REVERSE (FRONT (FRONT sbs)) *)
  metis_tac[TL_REVERSE_eq_REVERSE_FRONT]
QED

Theorem target_path_type_HashMapT_split_hashmap_subscripts:
  !env kt vt sbs ty.
    well_formed_vtype env.type_defs (HashMapT kt vt) ==>
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    split_hashmap_subscripts vt (TL (REVERSE sbs)) <> NONE
Proof
  rpt strip_tac >>
  `sbs <> []` by metis_tac[target_path_type_HashMapT_not_nil] >>
  drule_all target_path_type_Type_place_leaf_typed >>
  strip_tac >>
  gvs[place_leaf_typed_def] >>
  Cases_on `REVERSE sbs` >> gvs[place_leaf_path_typed_def] >>
  metis_tac[place_leaf_path_typed_imp_split_hashmap_subscripts]
QED

Theorem place_leaf_path_typed_split_leaf_type:
  !env vt path ty final_tv final_type key_types remaining.
    place_leaf_path_typed env vt path ty final_tv ==>
    split_hashmap_subscripts vt path = SOME (final_type, key_types, remaining) ==>
    ?base_tv.
      evaluate_type env.type_defs final_type = SOME base_tv ∧
      final_tv = leaf_type base_tv remaining ∧
      evaluate_type env.type_defs ty = SOME final_tv
Proof
  Induct_on `vt` >> rpt strip_tac >- (
    gvs[place_leaf_path_typed_def, split_hashmap_subscripts_def] >>
    qexists_tac `base_tv` >> simp[]) >>
  Cases_on `path` >> gvs[place_leaf_path_typed_def, split_hashmap_subscripts_def] >>
  rename1 `split_hashmap_subscripts vt t'` >>
  Cases_on `split_hashmap_subscripts vt t'` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  first_x_assum (qspecl_then [`env`,`t'`,`ty`,`final_tv`,`final_type`,`x1`,`remaining`] drule_all) >>
  strip_tac >>
  qexists_tac `base_tv` >> simp[]
QED

Theorem assign_operation_runtime_typed_Replace_from_value_has_type:
  !env ty tv v.
    evaluate_type env.type_defs ty = SOME tv ∧ value_has_type tv v ==>
    assign_operation_runtime_typed env ty (Replace v)
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
  metis_tac[]
QED


Theorem lookup_global_HashMapVarDecl_returns_HashMapRef:
  get_module_code cx src = SOME code ==>
  find_var_decl_by_name n code = SOME (HashMapVarDecl is_t kt vt, id) ==>
  lookup_var_slot_from_layout cx is_t src id = SOME slot ==>
  lookup_global cx src n st = (INL (HashMapRef is_t (n2w slot) kt vt), st)
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
     var_decl_info_CASE_rator, prod_CASE_rator, option_CASE_rator,
     type_value_CASE_rator, AllCaseEqs(), LET_THM] >>
  gvs[]
QED

Theorem target_path_type_HashMapT_assign_target_decomp:
  !env kt vt sbs ty.
    well_formed_vtype env.type_defs (HashMapT kt vt) ==>
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    ?first_sub rest_subs final_type kts remaining.
      REVERSE sbs = first_sub :: rest_subs ∧
      first_sub = LAST sbs ∧
      rest_subs = TL (REVERSE sbs) ∧
      split_hashmap_subscripts vt rest_subs = SOME (final_type, kts, remaining) ∧
      LENGTH kts + LENGTH remaining = LENGTH rest_subs ∧
      EVERY ((<>) NONE o subscript_to_value)
        (first_sub :: TAKE (LENGTH kts) rest_subs)
Proof
  rpt strip_tac >>
  `sbs <> []` by metis_tac[target_path_type_HashMapT_not_nil] >>
  `split_hashmap_subscripts vt (TL (REVERSE sbs)) <> NONE` by (
    drule_all target_path_type_HashMapT_split_hashmap_subscripts >> simp[]) >>
  Cases_on `split_hashmap_subscripts vt (TL (REVERSE sbs))` >- gvs[] >>
  PairCases_on `x` >>
  `LENGTH x1 + LENGTH x2 = LENGTH (TL (REVERSE sbs))` by (
    drule split_hashmap_subscripts_some_imp >> simp[]) >>
  `EVERY ((<>) NONE o subscript_to_value)
    (LAST sbs :: TAKE (LENGTH x1) (TL (REVERSE sbs)))` by (
    drule_all target_path_type_HashMapT_hashmap_prefix_ValueSubscript >> simp[]) >>
  `REVERSE sbs = LAST sbs :: TL (REVERSE sbs)` by (
    `REVERSE sbs = LAST sbs :: REVERSE (FRONT sbs)` by
      metis_tac[SNOC_LAST_FRONT_eq, REVERSE_SNOC_eq] >>
    `TL (REVERSE sbs) = REVERSE (FRONT sbs)` by
      metis_tac[TL_REVERSE_eq_REVERSE_FRONT] >>
    simp[]) >>
  qexistsl [`LAST sbs`, `TL (REVERSE sbs)`, `x0`, `x1`, `x2`] >>
  simp[]
QED

Theorem target_path_type_HashMapT_split_leaf_runtime:
  !env cx st kt vt sbs ty rest_subs final_type kts remaining.
    runtime_consistent env cx st ==>
    well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
    target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
    rest_subs = TL (REVERSE sbs) ==>
    split_hashmap_subscripts vt rest_subs = SOME (final_type, kts, remaining) ==>
    assignable_type (get_tenv cx) ty ==>
    ?final_tv.
      evaluate_type (get_tenv cx) final_type = SOME final_tv ∧
      evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) ∧
      leaf_type final_tv remaining ≠ NoneTV ∧
      well_formed_type_value final_tv
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `well_formed_vtype env.type_defs (HashMapT kt vt)` by metis_tac[] >>
  `sbs ≠ []` by metis_tac[target_path_type_HashMapT_not_nil] >>
  (* Get place_leaf_typed from target_path_type, then unfold to place_leaf_path_typed *)
  `?pl_tv. place_leaf_typed env (HashMapT kt vt) sbs ty pl_tv` by (
    irule target_path_type_Type_place_leaf_typed >> simp[]) >>
  gvs[place_leaf_typed_def] >>
  (* Now: place_leaf_path_typed env (HashMapT kt vt) (REVERSE sbs) ty pl_tv *)
  (* Case-split REVERSE sbs: [] contradicts sbs ≠ []; h::t gives the HashMapT case *)
  Cases_on `REVERSE sbs` >- gvs[] >>
  gvs[place_leaf_path_typed_def] >>
  (* Now: place_leaf_path_typed env vt t ty pl_tv, rest_subs = t *)
  (* Apply place_leaf_path_typed_split_leaf_type *)
  drule_all place_leaf_path_typed_split_leaf_type >>
  strip_tac >>
  qexists_tac `base_tv` >>
  (* Conjunct 1: evaluate_type (get_tenv cx) final_type = SOME base_tv *)
  conj_tac >- metis_tac[] >>
  (* Conjunct 2: evaluate_type (get_tenv cx) ty = SOME (leaf_type base_tv remaining) *)
  conj_tac >- metis_tac[] >>
  (* Conjunct 3: leaf_type base_tv remaining <> NoneTV *)
  conj_tac >- (
    irule assignable_type_evaluate_not_NoneTV >>
    metis_tac[]) >>
  (* Conjunct 4: well_formed_type_value base_tv *)
  irule evaluate_type_well_formed_type_value >>
  metis_tac[]
QED


Theorem resolve_array_element_error_sc:
  !a b c d e f g h. resolve_array_element a b c d e f = (INR g, h) ==> ?m. g = Error m
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rw[resolve_array_element_def, bind_apply, ignore_bind_apply, check_def,
     assert_def, return_def, raise_def, AllCaseEqs(), bound_CASE_rator] >>
  gvs[] >- (
    first_x_assum irule >>
    qexists_tac`0` >> simp[] >>
    goal_assum drule
  )
  >- (
    first_x_assum irule >>
    qexists_tac`1` >> simp[] >>
    goal_assum drule
  ) >>
  gvs[oneline get_storage_backend_def, COND_RATOR, AllCaseEqs(),
      bind_apply, return_def, get_transient_storage_def,
      get_accounts_def]
QED

Theorem resolve_array_element_error_not_TypeError[local]:
  !cx is_transient base_slot tv subs st e st'.
    leaf_type tv subs <> NoneTV ==>
    resolve_array_element cx is_transient base_slot tv subs st = (INR (Error e), st') ==>
    !msg. e <> TypeError msg
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  pop_assum mp_tac >>
  simp[Once resolve_array_element_def, bind_apply, ignore_bind_apply, check_def,
       assert_def, return_def, raise_def, AllCaseEqs(), bound_CASE_rator] >>
  rpt strip_tac >> gvs[leaf_type_def] >-
  (* Goal 1: Fixed case - check succeeds, recursive call returns TypeError.
     IH with elem_offset=0 says recursive call error is not TypeError.
     Provide witnesses for the existential goal. *)
   (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
    qexistsl [`s''`, `TypeError msg`, `st'`] >> simp[]) >-
  (* Goal 2: Dynamic case - storage + length checks succeed, recursive call TypeError.
     IH with elem_offset=1 says recursive call error is not TypeError. *)
   (first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
    qexistsl [`s''`, `TypeError msg`, `st'`] >> simp[]) >>
  (* Goal 3: Dynamic case - get_storage_backend returns INR (TypeError). Impossible:
     get_storage_backend always returns INL (it just reads state). *)
  gvs[oneline get_storage_backend_def, COND_RATOR, AllCaseEqs(),
      bind_apply, return_def, get_transient_storage_def,
      get_accounts_def]
QED

Theorem resolve_array_element_leaf_type_sc[local]:
  !cx b base tv subs st.
    !slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    leaf_type tv subs = leaf_type final_tv rsubs
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  gvs[leaf_type_def] >>
  FIRST [
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >> disch_then drule >> simp[],
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >> disch_then drule >> simp[]
  ]
QED

Theorem resolve_array_element_leaf_type_eq[local]:
  !cx b base tv subs st slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    leaf_type tv subs = leaf_type final_tv rsubs
Proof
  metis_tac[resolve_array_element_leaf_type_sc]
QED

Theorem resolve_array_element_ArrayTV_empty_rsubs_sc:
  !cx b base tv subs st.
    !slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    !etv ebd. final_tv = ArrayTV etv ebd ==> rsubs = []
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  gvs[] >>
  FIRST [
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >> disch_then drule >> simp[],
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >> disch_then drule >> simp[]
  ]
QED

Theorem resolve_array_element_well_formed_sc[local]:
  !cx b base tv subs st.
    !slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    well_formed_type_value tv ==> well_formed_type_value final_tv
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  gvs[well_formed_type_value_def] >>
  FIRST [
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >> disch_then drule >> simp[],
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >> disch_then drule >> simp[]
  ]
QED

Theorem resolve_array_element_well_formed_eq[local]:
  !cx b base tv subs st slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st = (INL (slot, final_tv, rsubs), st') ==>
    well_formed_type_value tv ==>
    well_formed_type_value final_tv
Proof
  metis_tac[resolve_array_element_well_formed_sc]
QED


Theorem storage_array_append_len_value_has_type:
  !stored_len n.

    stored_len < n ==>
    n < 2 ** 256 ==>
    value_has_type (BaseTV (UintT 256)) (IntV (&(stored_len + 1)))
Proof
  rewrite_tac[value_has_type_def, integerTheory.NUM_OF_INT, integerTheory.INT_POS] >>
  rpt strip_tac >>
  `stored_len + 1 <= n` by decide_tac >>
  `stored_len + 1 < 2 ** 256` by metis_tac[arithmeticTheory.LESS_OR_EQ, arithmeticTheory.LESS_TRANS] >>
  asm_rewrite_tac[]
QED

Theorem storage_array_pop_len_value_has_type:
  !stored_len.
    0 < stored_len ==>
    stored_len < 2 ** 256 ==>
    value_has_type (BaseTV (UintT 256)) (IntV (&(stored_len - 1)))
Proof
  rewrite_tac[value_has_type_def, integerTheory.NUM_OF_INT, integerTheory.INT_POS] >>
  rpt strip_tac >>
  `stored_len - 1 < stored_len` by decide_tac >>
  `stored_len - 1 < 2 ** 256` by metis_tac[arithmeticTheory.LESS_TRANS] >>
  asm_rewrite_tac[]
QED



Theorem top_level_HashMapT_not_storage_decl:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (HashMapT kt vt) ==>
  get_module_code cx src = SOME ts ==>
  find_var_decl_by_name n ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
  F
Proof
  rpt strip_tac >>
  `?is_tr ids. find_var_decl_by_name n ts = SOME (HashMapVarDecl is_tr kt vt, ids)`
    by metis_tac[top_level_HashMap_decl] >>
  pop_assum strip_assume_tac >>
  gvs[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_distinct]
QED


Theorem read_result_preserves_type:
  state_well_typed st /\ value_result_typed tvl tv /\ well_formed_type_value tv /\
  read_result cx tvl st = (INL v, st') ==>
  state_well_typed st' /\ value_has_type tv v
Proof
  rpt strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `tvl` >>
  gvs[read_result_def, bind_def, return_def, raise_def,
      value_result_typed_def, AllCaseEqs()] >>
  metis_tac[read_storage_slot_success_type, well_formed_type_value_def]
QED

Theorem read_value_result_preserves_type:
  value_result_typed (Value v) tv ==> value_has_type tv v
Proof
  simp[value_result_typed_def]
QED

(* eval_for preservation depends on statement-list soundness and therefore lives
   in vyperTypeStmtSoundnessScript.sml to avoid a StatePreservation ->
   StmtSoundness -> StatePreservation cycle. *)



(* Weak wrappers without shape/context premises - derived directly from the
   mutual theorem.  C5 statement branches that only need preservation can use
   these without deriving assign_operation_matches_target_shape or
   assign_target_assignable_context. *)
