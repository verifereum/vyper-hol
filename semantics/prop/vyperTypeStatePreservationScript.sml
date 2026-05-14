(*
 * State-update preservation lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeStatePreservation
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperStorageBackend vyperLookup vyperEncodeDecode vyperArith vyperAssignPreservesType
  vyperTypeSystem vyperTypeValues vyperTypeDefaults
  vyperScopePreservation vyperImmutablesPreservation vyperLookupStorage
  vyperStatePreservation vyperTypeEnv vyperTypeABI vyperTypeBuiltins vyperTypeExprSoundness
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
  env_consistent env cx st /\ string_to_num id NOTIN FDOM env.var_types /\
  new_variable id tv v st = (INR (Error e), st') ==>
  !msg. e <> TypeError msg
Proof
  rw[new_variable_def, bind_apply, ignore_bind_apply, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, assert_def, AllCaseEqs(),
     LET_THM, list_CASE_rator] >>
  gvs[env_consistent_def, env_scopes_consistent_def, optionTheory.IS_SOME_EXISTS, TO_FLOOKUP] >>
  Cases_on `lookup_scopes (string_to_num id) st.scopes` >> gvs[] >>
  qpat_x_assum `!id entry. lookup_scopes id st.scopes = SOME entry ==> _`
    (qspecl_then [`string_to_num id`, `x`] mp_tac) >> simp[TO_FLOOKUP]
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
  rw[] >> TRY (irule truncate_signed_range >> simp[])
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
  scope_well_typed (sc |+ (n, entry with value := v))
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
    lookup_scopes n (pre ++ (sc |+ (n, entry with value := v))::rest) =
    SOME (entry with value := v) /\
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
    lookup_scopes id (pre ++ (sc |+ (n, entry with value := v))::rest) =
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
    (st with scopes := pre ++ (sc |+ (n, entry with value := v))::rest)
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
      qexists_tac `entry with value := v` >> gvs[]) >>
    drule_all lookup_scopes_update_existing_value_other >> strip_tac >> gvs[] >>
    goal_assum drule >> simp[])
QED

Theorem env_consistent_update_existing_scope_value:
  env_consistent env cx (st with scopes := pre ++ sc::rest) /\
  lookup_scopes n pre = NONE /\ FLOOKUP sc n = SOME entry ==>
  env_consistent env cx
    (st with scopes := pre ++ (sc |+ (n, entry with value := v))::rest)
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
  state_well_typed st /\ lookup_scopes (string_to_num id) st.scopes = SOME entry /\
  value_has_type entry.type v ==>
  state_well_typed (update_name st id v)
Proof
  rw[update_name_def] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[]
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

Theorem assign_result_preserves_state:
  assign_result tv op old_val subs st = (res, st') ==> st' = st
Proof
  Cases_on `op` >>
  rw[assign_result_def, bind_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
  qpat_x_assum `(case evaluate_subscripts _ _ _ of _ => _) _ = _` mp_tac >>
  Cases_on `evaluate_subscripts tv old_val subs` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(case popped_value _ of _ => _) _ = _` mp_tac >>
  Cases_on `popped_value arr` >> gvs[return_def, raise_def]
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

Theorem assign_operation_leaf_type_update:
  evaluate_type env.type_defs ty = SOME leaf_tv /\
  assign_operation_runtime_typed env ty (Update upd_ty bop nv) /\
  value_has_type leaf_tv la /\
  assign_subscripts leaf_tv la [] (Update upd_ty bop nv) = INL lv ==>
  value_has_type leaf_tv lv
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >> gvs[] >>
  gvs[Once assign_subscripts_def, LET_THM] >>
  irule well_typed_binop_success_type >>
  qexists_tac `bop` >> qexists_tac `ty` >> qexists_tac `rhs_ty` >>
  qexists_tac `env.type_defs` >> qexists_tac `leaf_tv` >> qexists_tac `tv` >>
  qexists_tac `ty` >> qexists_tac `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u` >>
  qexists_tac `la` >> qexists_tac `nv` >>
  simp[]
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

Theorem assign_operation_leaf_update:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (Update upd_ty bop nv) /\
  value_has_type final_tv la /\
  assign_subscripts final_tv la [] (Update upd_ty bop nv) = INL lv ==>
  value_has_type final_tv lv
Proof
  metis_tac[assign_operation_leaf_type_update, place_leaf_typed_evaluate_type]
QED

Theorem location_runtime_typed_well_formed_vtype:
  runtime_consistent env cx st /\
  location_runtime_typed env cx st loc vt ==>
  well_formed_vtype env.type_defs vt
Proof
  rw[] >> Cases_on `loc` >> gvs[location_runtime_typed_def, well_formed_vtype_def]
  >- (
    fs[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def] >>
    first_x_assum drule >> strip_tac >> gvs[well_formed_type_def])
  >- (
    fs[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def,
       well_formed_type_def] >>
    simp[]) >>
  fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def,
     well_formed_vtype_def, well_formed_type_def] >>
  first_x_assum drule >> simp[]
QED

Theorem target_runtime_typed_place_leaf_typed:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty (BaseTargetV loc sbs) ==>
  ?vt final_tv. location_runtime_typed env cx st loc vt /\
                target_path_type env vt sbs (Type ty) /\
                place_leaf_typed env vt sbs ty final_tv
Proof
  Cases_on `tgt` >> rw[target_runtime_typed_def] >>
  qexists_tac `vt` >> simp[] >>
  irule target_path_type_Type_place_leaf_typed >> simp[] >>
  irule location_runtime_typed_well_formed_vtype >> metis_tac[]
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
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
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
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
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
  FLOOKUP env.bare_globals (env.current_src,n) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  set_immutable cx (current_module cx) n tv v st = (res, st') ==>
  env_consistent env cx st'
Proof
  rw[set_immutable_def, get_address_immutables_def, bind_def, lift_option_def,
     set_address_immutables_def, return_def, raise_def, AllCaseEqs(), LET_THM] >>
  qpat_x_assum `(case ALOOKUP _ _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `ALOOKUP _ _ = SOME _` assume_tac >>
  gvs[env_consistent_def] >>
  `current_module cx = env.current_src` by gvs[env_context_consistent_def] >>
  pop_assum SUBST_ALL_TAC >>
  conj_tac >- (gvs[env_scopes_consistent_def] >> metis_tac[] ) >>
  gvs[env_immutables_consistent_def, FLOOKUP_UPDATE] >>
  conj_tac >- rw[] >>
  conj_tac >- (
    reverse $ rw[] >> gvs[] >- metis_tac[] >>
    NO_TAC) >>
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
  rw[set_immutable_def, get_address_immutables_def, bind_def, lift_option_def,
     set_address_immutables_def, return_def, raise_def, AllCaseEqs(), LET_THM] >>
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

Theorem target_values_runtime_typed_LIST_REL3:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs =
    LIST_REL3 (\tgt ty gv. target_runtime_typed env cx st tgt ty gv) tgts tys gvs
Proof
  Induct_on `tgts` >> Cases_on `tys` >> Cases_on `gvs` >>
  simp[target_runtime_typed_def, LIST_REL3_def]
QED

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

Definition target_assignment_values_typed_def:
  target_assignment_values_typed env cx st tgts gvs vs <=>
    LIST_REL3 (\tgt gv v. ?ty tv.
      target_runtime_typed env cx st tgt ty gv /\
      evaluate_type env.type_defs ty = SOME tv /\
      value_has_type tv v) tgts gvs vs
End

Definition target_assignment_values_assignable_def:
  target_assignment_values_assignable env cx st tgts gvs vs <=>
    LIST_REL3 (\tgt gv v. ?ty tv.
      target_runtime_typed env cx st tgt ty gv /\
      assignable_type env.type_defs ty /\
      evaluate_type env.type_defs ty = SOME tv /\
      value_has_type tv v) tgts gvs vs
End

Theorem target_assignment_values_assignable_typed:
  target_assignment_values_assignable env cx st tgts gvs vs ==>
  target_assignment_values_typed env cx st tgts gvs vs
Proof
  rw[target_assignment_values_assignable_def, target_assignment_values_typed_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`vs`, `gvs`] >>
  Induct_on `tgts` >> Cases_on `gvs` >> Cases_on `vs` >>
  simp[LIST_REL3_def] >> metis_tac[]
QED

Theorem target_assignment_values_typed_shapes:
  target_assignment_values_typed env cx st tgts gvs vs ==>
  target_values_shape env tgts gvs
Proof
  rw[target_assignment_values_typed_def, target_values_shape_LIST_REL] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`vs`, `gvs`] >>
  Induct_on `tgts` >> Cases_on `gvs` >> Cases_on `vs` >>
  simp[LIST_REL3_def, target_runtime_typed_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >>
  simp[target_runtime_typed_def] >>
  `target_value_shape env h'' h` by (
    Cases_on `h''` >> Cases_on `h` >> gvs[target_runtime_typed_def]) >>
  strip_tac >> simp[]
QED

Theorem target_runtime_typed_rebuild_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv ==>
     !st'. runtime_consistent env cx st' ==>
           target_runtime_typed env cx st' tgt ty gv) /\
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs ==>
     !st'. runtime_consistent env cx st' ==>
           target_values_runtime_typed env cx st' tgts tys gvs)
Proof
  ho_match_mp_tac target_runtime_typed_ind >> rw[target_runtime_typed_def] >>
  Cases_on `loc` >> gvs[location_runtime_typed_def, runtime_consistent_def, env_consistent_def,
                         env_scopes_consistent_def, env_immutables_consistent_def]
  >- (
    rename1 `FLOOKUP env.var_types (string_to_num s) = SOME var_ty` >>
    `?entry'. lookup_scopes (string_to_num s) st'.scopes = SOME entry'` by metis_tac[IS_SOME_EXISTS] >>
    `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
    `evaluate_type (get_tenv cx) var_ty = SOME entry'.type` by metis_tac[] >>
    `entry'.type = entry.type` by gvs[] >>
    qexists_tac `Type var_ty` >> simp[])
  >- (
    rename1 `FLOOKUP env.bare_globals (_,string_to_num s) = SOME imm_ty` >>
    `env.current_src = current_module cx` by fs[env_context_consistent_def] >> gvs[] >>
    `?pair. FLOOKUP (get_source_immutables (current_module cx)
        (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m))
        (string_to_num s) = SOME pair` by metis_tac[IS_SOME_EXISTS] >>
    PairCases_on `pair` >>
    `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
    `evaluate_type (get_tenv cx) imm_ty = SOME pair0` by metis_tac[] >>
    qexists_tac `Type imm_ty` >> simp[] >>
    qexists_tac `get_source_immutables (current_module cx)
        (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m)` >>
    qexists_tac `pair1` >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
    Cases_on `ALOOKUP x (current_module cx)` >>
    gvs[get_immutables_def, get_address_immutables_def, bind_def, return_def,
        lift_option_def, get_source_immutables_def, AllCaseEqs()]) >>
  metis_tac[] >>
  NO_TAC
QED

Theorem target_runtime_typed_rebuild:
  runtime_consistent env cx st' /\ target_runtime_typed env cx st tgt ty gv ==>
  target_runtime_typed env cx st' tgt ty gv
Proof
  metis_tac[target_runtime_typed_rebuild_mutual]
QED

Theorem target_values_runtime_typed_rebuild:
  runtime_consistent env cx st' /\ target_values_runtime_typed env cx st tgts tys gvs ==>
  target_values_runtime_typed env cx st' tgts tys gvs
Proof
  metis_tac[target_runtime_typed_rebuild_mutual]
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

Theorem target_assignment_values_typed_rebuild:
  runtime_consistent env cx st' /\
  target_assignment_values_typed env cx st tgts gvs vs ==>
  target_assignment_values_typed env cx st' tgts gvs vs
Proof
  rw[target_assignment_values_typed_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`vs`, `gvs`] >>
  Induct_on `tgts` >> Cases_on `gvs` >> Cases_on `vs` >>
  simp[LIST_REL3_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[target_runtime_typed_rebuild]
QED

Definition assign_operation_matches_target_shape_def:
  assign_operation_matches_target_shape gv op <=>
    case gv of
    | BaseTargetV loc sbs => T
    | TupleTargetV gvs =>
        case op of
        | Replace (ArrayV (TupleV vs)) => LENGTH gvs = LENGTH vs
        | _ => F
End

Definition assign_target_assignable_def:
  assign_target_assignable (BaseTargetV loc sbs) st =
    (case loc of
     | ScopedVar id =>
         ?pre env entry rest.
           find_containing_scope (string_to_num id) st.scopes =
             SOME (pre, env, entry, rest) /\
           entry.assignable
     | _ => T) /\
  assign_target_assignable (TupleTargetV tgts) st =
    EVERY (\tgt. assign_target_assignable tgt st) tgts
End

Definition assign_target_assignable_context_def:
  assign_target_assignable_context cx (BaseTargetV loc sbs) st =
    (assign_target_assignable (BaseTargetV loc sbs) st /\
     case loc of
     | TopLevelVar src id =>
         ?code p. get_module_code cx src = SOME code /\
                  find_var_decl_by_num (string_to_num id) code = SOME p /\
                  (case FST p of
                   | StorageVarDecl is_transient typ =>
                       IS_SOME (evaluate_type (get_tenv cx) typ) /\
                       IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
                   | HashMapVarDecl is_transient _ _ =>
                       sbs <> [] /\
                       IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))
     | _ => T) /\
  assign_target_assignable_context cx (TupleTargetV tgts) st =
    EVERY (\tgt. assign_target_assignable_context cx tgt st) tgts
End

Theorem assign_target_preserves_state_well_typed_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (res, st') ==>
    !env tgt ty.
      runtime_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op ==>
      runtime_consistent env cx st') /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (res, st') ==>
    !env tgts.
      runtime_consistent env cx st /\
      target_assignment_values_typed env cx st tgts gvs vs ==>
      runtime_consistent env cx st')
Proof
  ho_match_mp_tac assign_target_ind >>
  conj_tac >- suspend "ScopedVar" >>
  conj_tac >- suspend "TopLevelVar" >>
  conj_tac >- suspend "ImmutableVar" >>
  conj_tac >- suspend "TupleTargetV" >>
  (* Repeated assign_target fallback TypeError clauses generated from the
     catch-all equation.  These are all impossible under the INL-result
     hypothesis; keep them separate from the substantive cases above. *)
  rpt (conj_tac >- (rpt strip_tac >> gvs[Once assign_target_def, raise_def])) >>
  conj_tac >- (
    (* assign_targets [] [] *)
    rpt strip_tac >>
    gvs[Once assign_target_def, return_def]) >>
  conj_tac >- suspend "assign_targets_cons" >>
  (* assign_targets fallback TypeError; impossible under INL result *)
  rpt strip_tac >>
  gvs[Once assign_target_def, raise_def]
QED

Resume assign_target_preserves_state_well_typed_mutual[ScopedVar]:
  rpt strip_tac >>
  rename1 `assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res, st')` >>
  `?vt final_tv. location_runtime_typed env cx st (ScopedVar id) vt /\
                 target_path_type env vt sbs (Type ty) /\
                 place_leaf_typed env vt sbs ty final_tv` by
    metis_tac[target_runtime_typed_place_leaf_typed] >>
  gvs[location_runtime_typed_def] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(), option_CASE_rator, get_scopes_def] >>
  pairarg_tac >> gvs[] >>
  drule find_containing_scope_lookup >>
  strip_tac >> gvs[] >>
  gvs[bind_apply, assert_def] >>
  Cases_on`entry.assignable` >> gvs[] >>
  qpat_x_assum`_ = (res,_)`mp_tac >>
  reverse CASE_TAC >> gvs[raise_def, return_def]
  >- (strip_tac >> gvs[]) >>
  sg `value_has_type entry.type x` >- (
    gvs[place_leaf_typed_def, place_leaf_path_typed_def] >>
    irule assign_subscripts_preserves_type >> simp[] >>
    conj_asm1_tac >- (
      drule_then irule evaluate_type_well_formed_type_value  ) >>
    goal_assum $ drule_at Any >>
    conj_tac >- metis_tac[assign_operation_leaf_type_update] >>
    conj_tac >- metis_tac[assign_operation_leaf_type_append] >>
    conj_tac >- metis_tac[assign_operation_leaf_type_replace] >>
    gvs[runtime_consistent_def] >>
    drule_all lookup_scopes_state_well_typed_value_has_type >> simp[]
  ) >>
  drule find_containing_scope_structure >> strip_tac >> gvs[] >>
  drule find_containing_scope_pre_none >> strip_tac >> gvs[] >>
  simp[set_scopes_def, return_def, raise_def] >>
  strip_tac >>
  drule assign_result_preserves_state >>
  strip_tac >> gvs[] >>
  gvs[runtime_consistent_def] >>
  gvs[get_scopes_def, return_def, set_scopes_def] >>
  conj_tac >- (
    irule env_consistent_update_existing_scope_value >> simp[] >>
    irule env_consistent_record_update_same_scopes >> simp[] ) >>
  gvs[state_well_typed_def, EVERY_APPEND] >>
  irule scope_well_typed_update_value >> simp[]
QED

Resume assign_target_preserves_state_well_typed_mutual[TopLevelVar]:
  rpt strip_tac >>
  rename1 `assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (res, st')` >>
  `?vt final_tv. location_runtime_typed env cx st (TopLevelVar src id) vt /\
                 target_path_type env vt sbs (Type ty) /\
                 place_leaf_typed env vt sbs ty final_tv` by
    metis_tac[target_runtime_typed_place_leaf_typed] >>
  gvs[location_runtime_typed_def] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(), option_CASE_rator,
      toplevel_value_CASE_rator, sum_CASE_rator]
  >> imp_res_tac lookup_global_state
  >> imp_res_tac resolve_array_element_state
  >> imp_res_tac assign_result_preserves_state
  >> gvs[]
  >> TRY (
    drule set_global_preserves_env_consistent >>
    gvs[runtime_consistent_def] >>
    disch_then drule >> strip_tac >>
    drule set_global_preserves_state_well_typed >>
    drule set_global_preserves_accounts_well_typed >>
    simp[] >> strip_tac >> disch_then irule >> simp[] >>
    goal_assum drule )
  >> pairarg_tac >> gvs[]
  >- (
    gvs[bind_apply, AllCaseEqs(), return_def, raise_def,
        option_CASE_rator, sum_CASE_rator] >>
    imp_res_tac assign_result_preserves_state >>
    imp_res_tac read_storage_slot_state >> gvs[] >>
    drule_at(Pat`write_storage_slot`) write_storage_slot_preserves_accounts_well_typed >>
    drule write_storage_slot_preserves_env_consistent >>
    drule write_storage_slot_preserves_state_well_typed_any >>
    gvs[runtime_consistent_def])
  >> gvs[bind_apply, return_def, raise_def, lift_option_type_def,
         lift_sum_def, ignore_bind_def, assert_def, check_def, AllCaseEqs(),
         option_CASE_rator, type_value_CASE_rator, sum_CASE_rator,
         bound_CASE_rator, assign_operation_CASE_rator]
  >> imp_res_tac assign_result_preserves_state
  >> imp_res_tac read_storage_slot_state
  >> imp_res_tac get_storage_backend_state
  >> gvs[]
  >> TRY (
    qmatch_rename_tac`runtime_consistent env cx sg` >>
    qmatch_assum_rename_tac`write_storage_slot _ _ _ _ _ sf = (_,sg)` >>
    qmatch_assum_rename_tac`write_storage_slot _ _ _ _ _ se = (_,sf)` >>
    `(runtime_consistent env cx sf ⇒ runtime_consistent env cx sg) ∧
     runtime_consistent env cx sf` suffices_by (rw[] >> gvs[]) >>
    rpt strip_tac)
  >> qmatch_rename_tac`runtime_consistent _ _ sk`
  >> qpat_x_assum`write_storage_slot _ _ _ _ _ _ = (_,sk)`assume_tac
  >> drule write_storage_slot_preserves_env_consistent
  >> drule write_storage_slot_preserves_state_well_typed_any
  >> drule write_storage_slot_preserves_accounts_well_typed
  >> gvs[runtime_consistent_def]
QED

Resume assign_target_preserves_state_well_typed_mutual[ImmutableVar]:
  rpt strip_tac >>
  `?vt final_tv. location_runtime_typed env cx st (ImmutableVar id) vt /\
                 target_path_type env vt is (Type ty) /\
                 place_leaf_typed env vt is ty final_tv` by
    metis_tac[target_runtime_typed_place_leaf_typed] >>
  gvs[location_runtime_typed_def] >>
  sg `well_formed_type_value tv ∧ value_has_type tv v` >- (
    fs[runtime_consistent_def] >>
    gvs[env_consistent_def, env_immutables_consistent_def] >>
    first_x_assum drule >>
    gvs[get_immutables_def, bind_apply, return_def, AllCaseEqs()] >>
    gvs[get_address_immutables_def, AllCaseEqs(),
        option_CASE_rator, lift_option_def, raise_def, return_def] >>
    sg `current_module cx = env.current_src` >- (
      gvs[current_module_def, env_context_consistent_def] ) >>
    gvs[env_context_consistent_def] >> strip_tac >>
    drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
    drule_all imms_well_typed_get_source_immutables >> simp[]
      ) >> gvs[] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  rename1 `FLOOKUP imms (string_to_num id) = SOME tva` >>
  PairCases_on `tva` >>
  gvs[AllCaseEqs(), return_def, raise_def, sum_CASE_rator] >>
  gvs[runtime_consistent_def] >>
  `value_has_type tv a'` by (
    gvs[place_leaf_typed_def, place_leaf_path_typed_def] >>
    qspecl_then [`tv`, `v`, `REVERSE is`, `op`, `a'`] mp_tac
      assign_subscripts_preserves_type >>
    simp[] >>
    impl_tac >- (
      conj_tac >- metis_tac[assign_operation_leaf_type_replace] >>
      conj_tac >- metis_tac[assign_operation_leaf_type_update] >>
      metis_tac[assign_operation_leaf_type_append]) >>
    simp[]) >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  conj_tac >- (
    irule set_immutable_preserves_env_consistent >>
    qexists_tac `string_to_num id` >> qexists_tac `INL ()` >>
    qexists_tac `s''` >> qexists_tac `tv` >> qexists_tac `ty'` >>
    qexists_tac `a'` >>
    gvs[env_consistent_def, env_context_consistent_def] >>
    rpt strip_tac >> first_x_assum drule_all >> simp[])
  >- (conj_tac >- (
        irule set_immutable_preserves_state_well_typed >>
        qexists_tac `cx` >> qexists_tac `string_to_num id` >>
        qexists_tac `INL ()` >> qexists_tac `current_module cx` >>
        qexists_tac `s''` >> qexists_tac `tv` >> qexists_tac `a'` >>
        simp[]) >>
      qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
      simp[set_immutable_def, get_address_immutables_def, bind_def,
           lift_option_def, set_address_immutables_def, return_def,
           raise_def, AllCaseEqs(), LET_THM] >>
      strip_tac >> gvs[] >>
      qpat_x_assum `(case ALOOKUP _ _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
      Cases_on `ALOOKUP s''.immutables cx.txn.target` >>
      gvs[return_def, raise_def] >> strip_tac >> gvs[])
  >- (irule set_immutable_preserves_env_consistent >>
      qexists_tac `string_to_num id` >> qexists_tac `INR e` >>
      qexists_tac `s''` >> qexists_tac `tv` >> qexists_tac `ty'` >>
      qexists_tac `a'` >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[])
  >- (qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
      simp[set_immutable_def, get_address_immutables_def, bind_def,
           lift_option_def, set_address_immutables_def, return_def,
           raise_def, AllCaseEqs(), LET_THM] >>
      Cases_on `ALOOKUP s''.immutables cx.txn.target` >>
      gvs[return_def, raise_def] >> strip_tac >> gvs[]) >>
  gvs[set_immutable_def, get_address_immutables_def, bind_def,
      lift_option_def, set_address_immutables_def, return_def,
      raise_def, AllCaseEqs(), LET_THM]
QED

Resume assign_target_preserves_state_well_typed_mutual[TupleTargetV]:
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  Cases_on `tgt` >> gvs[target_runtime_typed_def, target_value_shape_def, well_typed_atarget_def,
      target_assignment_values_typed_def] >>
  first_x_assum drule >>
  simp[] >>
  strip_tac >>
  first_x_assum irule >>
  simp[target_assignment_values_typed_def] >>
  qexists_tac `l` >>
  gvs[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  gvs[value_has_type_def, values_have_types_LIST_REL] >>
  irule LIST_REL3_from_LIST_REL2 >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> rw[] >>
  pairarg_tac >> gvs[EL_ZIP] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `EL n tys` >>
  qexists_tac `EL n tvs` >>
  simp[] >>
  gvs[target_values_runtime_typed_LIST_REL3] >>
  drule LIST_REL3_EL >> simp[]
QED

Resume assign_target_preserves_state_well_typed_mutual[assign_targets_cons]:
  rpt strip_tac >>
  reverse $
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(), target_assignment_values_typed_def] >>
  Cases_on `tgts` >> gvs[LIST_REL3_def] >>
  first_x_assum (drule_then drule) >>
  simp[assign_operation_runtime_typed_def,
       value_runtime_typed_def, PULL_EXISTS] >>
  disch_then drule >> simp[] >> strip_tac >>
  first_x_assum (drule_then drule) >> simp[] >>
  disch_then irule >>
  `target_assignment_values_typed env cx st t gvs vs` by
    simp[target_assignment_values_typed_def] >>
  drule_all target_assignment_values_typed_rebuild >>
  simp[target_assignment_values_typed_def] >>
  strip_tac >> goal_assum drule
QED

Finalise assign_target_preserves_state_well_typed_mutual

Theorem assign_result_no_type_error_from_successful_assign:
  assign_subscripts tv old subs op = INL new /\
  assign_result tv op old subs st = (res, st') ==>
  no_type_error_result res
Proof
  Cases_on `op` >>
  simp[assign_result_def, return_def, bind_apply, no_type_error_result_def] >>
  rpt strip_tac >> gvs[] >>
  drule assign_subscripts_PopOp_assign_result >> strip_tac >>
  qpat_x_assum `(case lift_sum (evaluate_subscripts _ _ _) _ of _ => _) = _` mp_tac >>
  gvs[lift_sum_def, return_def, raise_def, AllCaseEqs(),
      sum_CASE_rator, popped_value_def] >>
  strip_tac >> gvs[]
QED

Theorem assign_result_no_type_error_from_successful_assign_split:
  assign_subscripts tv old subs op = INL new ==>
  assign_result tv op old subs st = (res, st') ==>
  no_type_error_result res
Proof
  Cases_on `op` >>
  simp[assign_result_def, return_def, bind_apply, no_type_error_result_def] >>
  rpt strip_tac >> gvs[] >>
  drule assign_subscripts_PopOp_assign_result >> strip_tac >>
  qpat_x_assum `(case lift_sum (evaluate_subscripts _ _ _) _ of _ => _) = _` mp_tac >>
  gvs[lift_sum_def, return_def, raise_def, AllCaseEqs(),
      sum_CASE_rator, popped_value_def] >>
  strip_tac >> gvs[]
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
  find_var_decl_by_num n ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
  typ = base_ty
Proof
  rw[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem top_level_Type_not_hashmap_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type base_ty) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_num n ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
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
    find_var_decl_by_num n ts = SOME (HashMapVarDecl is_transient kt vt,id_str)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  metis_tac[]
QED

Theorem top_level_vtype_well_formed:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME vt ==>
  well_formed_vtype env.type_defs vt
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  metis_tac[]
QED

Theorem target_runtime_typed_top_level_Type:
  target_runtime_typed env cx st tgt ty (BaseTargetV (TopLevelVar src id) sbs) /\
  FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type base_ty) ==>
  target_path_type env (Type base_ty) sbs (Type ty)
Proof
  Cases_on `tgt` >> rw[target_runtime_typed_def, location_runtime_typed_def] >> gvs[]
QED

Theorem lookup_global_Value_not_HashMapVarDecl:
  lookup_global cx src n st = (INL (Value v), st') /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME p /\
  FST p = HashMapVarDecl is_t kt vt ==>
  F
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, raise_def] >>
  gvs[return_def, AllCaseEqs(), option_CASE_rator, var_decl_info_CASE_rator,
      prod_CASE_rator] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient' src id` >>
  gvs[return_def, raise_def, bind_def]
QED

Theorem lookup_global_ArrayRef_not_HashMapVarDecl:
  lookup_global cx src n st = (INL (ArrayRef is_t bs etv ebd), st') ==>
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME p ==>
  FST p = HashMapVarDecl is_transient' kt vt ==>
  F
Proof
  rw[lookup_global_def, bind_def, lift_option_type_def, raise_def] >>
  gvs[return_def, AllCaseEqs(), option_CASE_rator, var_decl_info_CASE_rator,
      prod_CASE_rator, type_value_CASE_rator] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient'' src id` >>
  gvs[return_def, raise_def, bind_def]
QED

Theorem lookup_global_ArrayRef_not_StorageVarDecl:
  lookup_global cx src n st = (INL (ArrayRef is_t bs etv ebd), st') ==>
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient' typ, id) ==>
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  root_tv ≠ ArrayTV etv ebd ==>
  F
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM, AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem lookup_global_HashMapRef_not_StorageVarDecl:
  lookup_global cx src n st = (INL (HashMapRef is_t bs kt vt), st') ==>
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient' typ, id) ==>
  F
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, toplevel_value_CASE_rator, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem lookup_global_top_level_assignable_no_type_error:
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st =
    (INR (Error (TypeError msg)), st') ==>
  F
Proof
  strip_tac >>
  gvs[assign_target_assignable_context_def, assign_target_assignable_def] >>
  rename1 `get_module_code cx src = SOME code` >>
  rename1 `find_var_decl_by_num (string_to_num id) code = SOME p` >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, return_def, raise_def,
       lift_option_type_def, option_CASE_rator,
       var_decl_info_CASE_rator, prod_CASE_rator] >>
  simp[] >>
  Cases_on `p` >> gvs[] >>
  Cases_on `q` >> gvs[]
  >- (
    rename1 `StorageVarDecl is_transient typ` >>
    `?slot. lookup_var_slot_from_layout cx is_transient src r = SOME slot` by
      metis_tac[optionTheory.IS_SOME_EXISTS] >>
    `?tv. evaluate_type (get_tenv cx) typ = SOME tv` by
      metis_tac[optionTheory.IS_SOME_EXISTS] >>
    gvs[] >>
    Cases_on `tv` >> gvs[bind_def, return_def, raise_def]
    >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (BaseTV b) st` >>
        Cases_on `q` >> gvs[] >>
        drule read_storage_slot_error >> strip_tac >> gvs[])
    >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (TupleTV l) st` >>
        Cases_on `q` >> gvs[] >>
        drule read_storage_slot_error >> strip_tac >> gvs[])
    >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (StructTV l) st` >>
        Cases_on `q` >> gvs[] >>
        drule read_storage_slot_error >> strip_tac >> gvs[])
    >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (FlagTV n) st` >>
        Cases_on `q` >> gvs[] >>
        drule read_storage_slot_error >> strip_tac >> gvs[]) >>
    Cases_on `read_storage_slot cx is_transient (n2w slot) NoneTV st` >>
    Cases_on `q` >> gvs[] >>
    drule read_storage_slot_error >> strip_tac >> gvs[]) >>
  rename1 `HashMapVarDecl is_transient kt vt` >>
  `?slot. lookup_var_slot_from_layout cx is_transient src r = SOME slot` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  gvs[]
QED

Theorem lookup_global_storage_Value_typed:
  lookup_global cx src n st = (INL (Value old_v), st') /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  value_has_type tv old_v
Proof
  rw[] >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
       raise_def, option_CASE_rator, var_decl_info_CASE_rator,
       prod_CASE_rator] >>
  Cases_on `tv` >> gvs[return_def, raise_def, bind_def]
  >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (BaseTV b) st` >>
      Cases_on `q` >> gvs[] >> strip_tac >> gvs[] >>
      metis_tac[read_storage_slot_success_type])
  >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (TupleTV l) st` >>
      Cases_on `q` >> gvs[] >> strip_tac >> gvs[] >>
      metis_tac[read_storage_slot_success_type])
  >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (StructTV l) st` >>
      Cases_on `q` >> gvs[] >> strip_tac >> gvs[] >>
      metis_tac[read_storage_slot_success_type])
  >- (Cases_on `read_storage_slot cx is_transient (n2w slot) (FlagTV n') st` >>
      Cases_on `q` >> gvs[] >> strip_tac >> gvs[] >>
      metis_tac[read_storage_slot_success_type]) >>
  Cases_on `read_storage_slot cx is_transient (n2w slot) NoneTV st` >>
  Cases_on `q` >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[read_storage_slot_success_type, value_has_type_NoneTV]
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
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ,id_str) /\
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
    >- metis_tac[assign_operation_leaf_type_replace]
    >- metis_tac[assign_operation_leaf_type_update] >>
    metis_tac[assign_operation_leaf_type_append]) >>
  simp[]
QED

Theorem top_level_vtype_Type_storage_decl:
  runtime_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type root_ty) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ,id_str) ==>
  typ = root_ty
Proof
  strip_tac >>
  gvs[runtime_consistent_def, env_consistent_def, env_immutables_consistent_def] >>
  first_x_assum $ drule_then drule >>
  strip_tac >> first_x_assum drule >>
  rw[]
QED

Theorem top_level_storage_value_leaf_evaluate_type:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty (BaseTargetV (TopLevelVar src id) sbs) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ,id_str) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  evaluate_type env.type_defs ty = SOME (leaf_type tv (REVERSE sbs))
Proof
  rw[] >>
  `?loc_vt. location_runtime_typed env cx st (TopLevelVar src id) loc_vt /\
            target_path_type env loc_vt sbs (Type ty)` by
    (Cases_on `tgt` >> gvs[target_runtime_typed_def] >> metis_tac[]) >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME loc_vt` by
    gvs[location_runtime_typed_def] >>
  Cases_on `loc_vt` >> gvs[]
  >- (
    `typ = t` by metis_tac[top_level_vtype_Type_storage_decl] >>
    gvs[] >>
    `env.type_defs = get_tenv cx` by
      gvs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
    gvs[] >>
    `well_formed_vtype env.type_defs (Type t)` by
      metis_tac[top_level_vtype_well_formed] >>
    drule_all target_path_type_Type_place_leaf_typed >>
    strip_tac >>
    gvs[place_leaf_typed_def, place_leaf_path_typed_def]) >>
  drule_all top_level_HashMap_decl >>
  strip_tac >>
  gvs[]
QED

Theorem top_level_storage_value_set_global_no_type_error:
  lookup_global cx src n st = (INL (Value old_v), st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  evaluate_type env.type_defs leaf_ty = SOME (leaf_type tv subs) /\
  assign_subscripts tv old_v subs op = INL new_v /\
  assign_operation_runtime_typed env leaf_ty op /\
  set_global cx src n new_v st = (INR (Error (TypeError msg)), st') ==>
  F
Proof
  rpt strip_tac >>
  `value_has_type tv old_v` by
    metis_tac[lookup_global_storage_Value_typed] >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tv new_v` by
    metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
  metis_tac[set_global_storage_no_type_error]
QED

Theorem top_level_storage_value_set_global_no_type_error_pair:
  lookup_global cx src n st = (INL (Value old_v), st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME p /\
  FST p = StorageVarDecl is_transient typ /\
  lookup_var_slot_from_layout cx is_transient src (SND p) = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  evaluate_type env.type_defs leaf_ty = SOME (leaf_type tv subs) /\
  assign_subscripts tv old_v subs op = INL new_v /\
  assign_operation_runtime_typed env leaf_ty op /\
  set_global cx src n new_v st = (INR (Error (TypeError msg)), st') ==>
  F
Proof
  Cases_on `p` >> rw[] >>
  metis_tac[top_level_storage_value_set_global_no_type_error]
QED

Theorem top_level_storage_value_assign_success_no_type_error:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assign_operation_runtime_typed env ty op /\
  lookup_global cx src (string_to_num id) st =
    (INL (Value old_v), st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME root_tv /\
  assign_subscripts root_tv old_v (REVERSE sbs) op = INL new_v /\
  set_global cx src (string_to_num id) new_v st =
    (INR (Error (TypeError msg)), st') ==>
  F
Proof
  strip_tac >>
  drule_all lookup_global_storage_Value_typed >> strip_tac >>
  drule_all top_level_storage_value_leaf_evaluate_type >> strip_tac >>
  `well_formed_type_value root_tv` by (
    irule evaluate_type_well_formed_type_value >>
    goal_assum drule_all ) >>
  drule_all assign_subscripts_preserves_type_runtime_typed >> strip_tac >>
  qhdtm_x_assum`set_global`mp_tac >> simp[] >>
  irule set_global_storage_no_type_error >>
  goal_assum drule_all
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
  (* TODO: prove directly by binop-family inversion.  This is exactly the
     assignment-shaped instance of the existing builtin no-TypeError theorem. *)
  metis_tac[well_typed_binop_no_type_error]
QED

Theorem assign_subscripts_update_leaf_no_type_error:
  well_typed_binop lhs_ty bop lhs_ty rhs_ty /\
  evaluate_type tenv lhs_ty = SOME lhs_tv /\
  evaluate_type tenv rhs_ty = SOME rhs_tv /\
  value_has_type lhs_tv lhs /\
  value_has_type rhs_tv rhs ==>
  assign_subscripts lhs_tv lhs [] (Update lhs_ty bop rhs) <>
    INR (TypeError msg)
Proof
  simp[Once assign_subscripts_def, LET_THM] >>
  metis_tac[well_typed_update_binop_no_type_error]
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
    rename1 `Update upd_ty bop rhs` >>
    gvs[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
    drule_all assign_subscripts_update_leaf_no_type_error >> simp[]) >- (
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

Theorem top_level_storage_value_assign_subscripts_no_type_error:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assignable_type env.type_defs ty /\
  assign_operation_runtime_typed env ty op /\
  lookup_global cx src (string_to_num id) st =
    (INL (Value old_v), st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl is_transient typ,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  assign_subscripts root_tv old_v (REVERSE sbs) op <> INR (TypeError msg)
Proof
  strip_tac >>
  drule_all lookup_global_storage_Value_typed >> strip_tac >>
  drule_all top_level_storage_value_leaf_evaluate_type >> strip_tac >>
  `well_formed_type_value root_tv` by (
    irule evaluate_type_well_formed_type_value >>
    goal_assum drule_all ) >>
  `leaf_type root_tv (REVERSE sbs) <> NoneTV` by (
    drule_all assignable_type_evaluate_not_NoneTV >>
    simp[] ) >>
  irule assign_subscripts_no_type_error_runtime_typed >>
  simp[] >>
  goal_assum drule_all
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

Theorem assign_target_sound_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (res, st') ==>
    !env tgt ty.
      runtime_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\
      assignable_type env.type_defs ty /\
      assign_operation_runtime_typed env ty op /\
      assign_operation_matches_target_shape gv op /\
      assign_target_assignable_context cx gv st ==>
      runtime_consistent env cx st' /\ no_type_error_result res) /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (res, st') ==>
    !env tgts.
      runtime_consistent env cx st /\
      target_assignment_values_assignable env cx st tgts gvs vs /\
      EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
      runtime_consistent env cx st' /\ no_type_error_result res)
Proof
  ho_match_mp_tac assign_target_ind >>
  conj_tac >- suspend "sound_ScopedVar" >>
  conj_tac >- suspend "sound_TopLevelVar" >>
  conj_tac >- suspend "sound_ImmutableVar" >>
  conj_tac >- suspend "sound_TupleTargetV" >>
  rpt (conj_tac >- (
    rpt strip_tac >>
    gvs[Once assign_target_def, raise_def, no_type_error_result_def,
        target_runtime_typed_def, target_value_shape_def,
        assign_operation_runtime_typed_def, assign_operation_matches_target_shape_def,
        assign_target_assignable_context_def, assign_target_assignable_def, value_runtime_typed_def,
        value_has_type_def, evaluate_type_def, AllCaseEqs()] >>
    Cases_on `tgt` >> gvs[target_runtime_typed_def, evaluate_type_def, AllCaseEqs()] >>
    gvs[value_has_type_def, evaluate_type_def, AllCaseEqs()])) >>
  conj_tac >- (
    rpt strip_tac >>
    gvs[Once assign_target_def, return_def, no_type_error_result_def]) >>
  conj_tac >- suspend "sound_assign_targets_cons" >>
  rpt strip_tac >>
  gvs[Once assign_target_def, raise_def, no_type_error_result_def,
      target_assignment_values_assignable_def, LIST_REL3_def]
QED

Resume assign_target_sound_mutual[sound_ScopedVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    irule (cj 1 assign_target_preserves_state_well_typed_mutual) >>
    goal_assum drule_all >> simp[]) >>
  rename1 `assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res, st')` >>
  gvs[assign_target_assignable_context_def, assign_target_assignable_def] >>
  reverse $
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(), option_CASE_rator, get_scopes_def,
      no_type_error_result_def, sum_CASE_rator, set_scopes_def]
  >- (
    rpt strip_tac >>
    gvs[target_runtime_typed_def, target_value_shape_def, location_runtime_typed_def] >>
    gvs[runtime_consistent_def] >>
    drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
    `runtime_consistent env cx s''` by simp[runtime_consistent_def] >>
    `?vt final_tv. location_runtime_typed env cx s'' (ScopedVar id) vt /\
                   target_path_type env vt sbs (Type ty) /\
                   place_leaf_typed env vt sbs ty final_tv` by
      metis_tac[target_runtime_typed_place_leaf_typed] >>
    gvs[location_runtime_typed_def] >>
    `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by (
      irule scope_well_typed_lookup_scopes >>
      gvs[state_well_typed_def] >>
      goal_assum drule >> simp[]) >>
    gvs[place_leaf_typed_def, place_leaf_path_typed_def] >>
    Cases_on `REVERSE sbs = []` >- (
      gvs[leaf_type_def] >>
      qspecl_then [`env`,`ty`,`op`,`entry.type`,`entry.value`,`msg`]
        mp_tac assign_operation_runtime_typed_leaf_no_type_error >>
      simp[]) >>
    qspecl_then [`entry.type`,`entry.value`,`REVERSE sbs`,`op`,`env`,`ty`,`msg`]
      mp_tac assign_subscripts_no_type_error_runtime_typed >>
    impl_tac >- (
      simp[] >>
      drule_all assignable_type_evaluate_not_NoneTV >> simp[]) >>
    simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule assign_result_no_type_error_from_successful_assign >>
  disch_then drule >>
  simp[no_type_error_result_def]
QED

Theorem lookup_global_HashMapVarDecl_returns_HashMapRef:
  get_module_code cx src = SOME code ==>
  find_var_decl_by_num n code = SOME (HashMapVarDecl is_t kt vt, id) ==>
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

Theorem assign_target_HashMapRef_branch_no_type_error:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (HashMapRef is_transient (n2w slot) kt vt), st) ==>
  get_module_code cx src_id_opt = SOME code ==>
  env.type_defs = get_tenv cx ==>
  REVERSE sbs = first_sub :: rest_subs ==>
  split_hashmap_subscripts vt rest_subs = SOME (final_type, kts, remaining) ==>
  compute_hashmap_slot (n2w slot) (kt::kts)
    (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) = SOME final_slot ==>
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  well_formed_type_value final_tv ==>
  leaf_type final_tv remaining <> NoneTV ==>
  assign_operation_runtime_typed env ty op ==>
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, option_CASE_rator,
      sum_CASE_rator, pairTheory.PAIR,
      toplevel_value_CASE_rator, LET_THM,
      AllCaseEqs()] >-
  (* Goal 1: Full success path - assign_result *)
  (`value_has_type final_tv current_val` by
     (drule_all_then assume_tac read_storage_slot_success_type >> simp[]) >>
   `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` by metis_tac[] >>
   `value_has_type final_tv new_val` by
     metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
   drule assign_result_no_type_error_from_successful_assign >>
   disch_then drule >>
   simp[no_type_error_result_def])
  >-
  (* Goal 2: write_storage_slot INR - TypeError impossible when value typed *)
  (`value_has_type final_tv current_val` by
     (drule_all_then assume_tac read_storage_slot_success_type >> simp[]) >>
   `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` by metis_tac[] >>
   `value_has_type final_tv new_val` by
     metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
   simp[no_type_error_result_def] >>
   CCONTR_TAC >> gvs[] >>
   metis_tac[write_storage_slot_no_type_error_from_value_has_type])
  >-
  (* Goal 3: assign_subscripts INR - TypeError impossible by runtime typing *)
  (`value_has_type final_tv current_val` by
     (drule_all_then assume_tac read_storage_slot_success_type >> simp[]) >>
   `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` by metis_tac[] >>
   drule_all_then strip_assume_tac assign_subscripts_no_type_error_runtime_typed >>
   simp[no_type_error_result_def] >>
   metis_tac[])
  >-
  (* Goal 4: read_storage_slot INR - always RuntimeError, never TypeError *)
  (drule read_storage_slot_error >>
   rpt strip_tac >>
   simp[no_type_error_result_def])
QED


Theorem lookup_global_StorageVarDecl_ArrayTV_returns_ArrayRef:
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV elem_tv bd) ==>
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient (n2w slot) elem_tv bd), st)
Proof
  rpt strip_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       LET_THM, var_decl_info_CASE_rator, prod_CASE_rator, option_CASE_rator,
       type_value_CASE_rator, AllCaseEqs()]
QED

Theorem lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError:
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  root_tv ≠ ArrayTV elem_tv bd ==>
  lookup_global cx src_id_opt n st = (INR (Error (TypeError msg)), st') ==>
  F
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       LET_THM, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[] >>
  (* For each non-ArrayTV subtype, read_storage_slot cannot return TypeError *)
  rpt strip_tac >>
  Cases_on `read_storage_slot cx is_transient (n2w slot) root_tv st` >> gvs[] >>
  imp_res_tac read_storage_slot_error >> gvs[]
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

Theorem resolve_array_element_ArrayTV_empty_rsubs_sc[local]:
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

Theorem assign_target_ArrayRef_checkpoint_break:
  T
Proof
  simp[]
QED

Theorem storage_array_append_len_value_has_type[local]:
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

Theorem storage_array_pop_len_value_has_type[local]:
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

Theorem assign_target_ArrayRef_ordinary_checkpoint_break[local]:
  T
Proof
  simp[]
QED

Theorem assign_target_TopLevelVar_ArrayRef_ordinary_no_type_error[local]:
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient base_slot elem_tv bd), st) ==>
  get_module_code cx src_id_opt = SOME code ==>
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE sbs) st =
    (INL (elem_slot, final_tv, remaining_subs), st_res) ==>
  op <> PopOp ==>
  (!v. op <> AppendOp v) ==>
  well_formed_type_value final_tv ==>
  assign_operation_runtime_typed env ty op ==>
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining_subs) ==>
  leaf_type final_tv remaining_subs <> NoneTV ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  cheat
QED

Theorem assign_target_TopLevelVar_ArrayRef_branch_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) ==>
  target_path_type env (Type t) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  env.type_defs = get_tenv cx ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV elem_tv bd) ==>
  lookup_global cx src_id_opt (string_to_num id) st =
    (INL (ArrayRef is_transient (n2w slot) elem_tv bd), st) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `well_formed_vtype env.type_defs (Type t)` by metis_tac[top_level_vtype_well_formed] >>
  `typ = t` by metis_tac[top_level_Type_storage_decl] >>
  fs[] >>
  `well_formed_type_value (ArrayTV elem_tv bd)`
    by metis_tac[evaluate_type_well_formed_type_value] >>
  `evaluate_type env.type_defs ty = SOME (leaf_type (ArrayTV elem_tv bd) (REVERSE sbs))`
    by metis_tac[target_path_type_Type_evaluate_leaf] >>
  `leaf_type (ArrayTV elem_tv bd) (REVERSE sbs) <> NoneTV`
    by metis_tac[target_path_type_Type_evaluate_leaf_not_NoneTV] >>
  qpat_x_assum `assign_target _ _ _ _ = (_,_)` mp_tac >>
  simp[Once assign_target_def, bind_def, lift_option_type_def, return_def, raise_def,
       LET_THM, pairTheory.PAIR, option_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, toplevel_value_CASE_rator, var_decl_info_CASE_rator,
       sum_CASE_rator, ignore_bind_def, type_check_def] >>
  Cases_on `resolve_array_element cx is_transient (n2w slot) (ArrayTV elem_tv bd) (REVERSE sbs) st` >>
  Cases_on `q` >> gvs[] >-
  (* INL: resolve_array_element succeeds *)
  (PairCases_on `x` >> gvs[] >>
   (* x = (x0,x1,x2) where x0=elem_slot, x1=final_tv, x2=remaining_subs *)
   (* Derive typing facts about final_tv (x1) and remaining (x2) *)
   `well_formed_type_value x1`
     by metis_tac[resolve_array_element_well_formed_sc] >>
   `evaluate_type env.type_defs ty = SOME (leaf_type x1 x2)`
     by metis_tac[resolve_array_element_leaf_type_sc] >>
   `leaf_type x1 x2 <> NoneTV`
     by metis_tac[resolve_array_element_leaf_type_sc] >>
   `!etv ebd. x1 = ArrayTV etv ebd ==> x2 = []`
     by metis_tac[resolve_array_element_ArrayTV_empty_rsubs_sc] >>
   (* Split on type_value constructor to separate branches *)
   Cases_on `x1` >>
   (* For all non-ArrayTV-Dynamic constructors, the code path is:
      read_storage_slot -> lift_sum assign_subscripts -> write_storage_slot -> assign_result.
      Use a uniform tactic for these. *)
   TRY (
     gvs[bind_def, lift_sum_def, return_def, raise_def, AllCaseEqs(),
         no_type_error_result_def, assign_result_def] >>
     rpt (FIRST [
       (* success path: assign_result returns non-TypeError *)
       simp[no_type_error_result_def],
       (* assign_subscripts INR: not TypeError *)
       metis_tac[assign_subscripts_no_type_error_runtime_typed],
       (* write_storage_slot INR: need value_has_type first *)
       (CCONTR_TAC >> gvs[] >>
        metis_tac[assign_subscripts_preserves_type_runtime_typed,
                  write_storage_slot_no_type_error_from_value_has_type]),
       (* read_storage_slot INR: always RuntimeError *)
       (drule read_storage_slot_error >> simp[no_type_error_result_def])
     ])
   ) >>
   (* ArrayTV: split on bound *)
   rename1 `ArrayTV etv' abd` >>
   Cases_on `abd` >> gvs[well_formed_type_value_def] >-
   (* ArrayTV Fixed: same pattern as non-ArrayTV *)
   (gvs[bind_def, lift_sum_def, return_def, raise_def, AllCaseEqs(),
        no_type_error_result_def, assign_result_def] >>
    rpt (FIRST [
      simp[no_type_error_result_def],
      metis_tac[assign_subscripts_no_type_error_runtime_typed],
      (CCONTR_TAC >> gvs[] >>
       metis_tac[assign_subscripts_preserves_type_runtime_typed,
                 write_storage_slot_no_type_error_from_value_has_type]),
      (drule read_storage_slot_error >> simp[no_type_error_result_def])
    ])) >>
   (* ArrayTV Dynamic: split on operation *)
   Cases_on `op` >>
   TRY (
     (* Replace/Update: same pattern *)
     gvs[bind_def, lift_sum_def, return_def, raise_def, AllCaseEqs(),
         no_type_error_result_def, assign_result_def] >>
     rpt (FIRST [
       simp[no_type_error_result_def],
       metis_tac[assign_subscripts_no_type_error_runtime_typed],
       (CCONTR_TAC >> gvs[] >>
        metis_tac[assign_subscripts_preserves_type_runtime_typed,
                  write_storage_slot_no_type_error_from_value_has_type]),
       (drule read_storage_slot_error >> simp[no_type_error_result_def])
     ])
   ) >>
   (* AppendOp: check + 2 writes + return NONE *)
   gvs[assign_operation_runtime_typed_def, bind_def, lift_sum_def, return_def,
       raise_def, get_storage_backend_def, check_def, assert_def, AllCaseEqs(),
       no_type_error_result_def, type_slot_size_def, default_value_def,
       vfmStateTheory.lookup_storage_def] >-
   (* All writes succeed *)
   simp[no_type_error_result_def] >-
   (* Second write INR: write length BaseTV(UintT 256) IntV *)
   (CCONTR_TAC >> gvs[] >>
    FAIL_TAC "probe_append_write2_arith") >-
   (* First write INR: write element elem_tv v *)
   (CCONTR_TAC >> gvs[] >>
    metis_tac[write_storage_slot_no_type_error_from_value_has_type]) >-
   (* Check fails *)
   simp[no_type_error_result_def] >>
   (* PopOp: check + read + 2 writes + ret *)
   gvs[assign_operation_runtime_typed_def, bind_def, lift_sum_def, return_def,
       raise_def, get_storage_backend_def, check_def, assert_def, AllCaseEqs(),
       no_type_error_result_def, type_slot_size_def, default_value_def,
       vfmStateTheory.lookup_storage_def] >-
   (* All succeed *)
   simp[no_type_error_result_def] >-
   (* Last write INR: length BaseTV(UintT 256) IntV *)
   (CCONTR_TAC >> gvs[] >>
    FAIL_TAC "probe_pop_write2_arith") >-
   (* Default write INR: write default_value pop_elem_tv *)
   (CCONTR_TAC >> gvs[] >>
    metis_tac[write_storage_slot_no_type_error_from_value_has_type,
              default_value_has_type]) >-
   (* Read INR *)
   (drule read_storage_slot_error >> simp[no_type_error_result_def]) >-
   (* Check fails *)
   simp[no_type_error_result_def]
  ) >>
  (* INR: resolve_array_element error - always RuntimeError, never TypeError *)
  drule resolve_array_element_error_sc >> rpt strip_tac >>
  Cases_on `g` >> gvs[no_type_error_result_def]
QED

Theorem assign_target_TopLevelVar_Value_branch_ntr:
  (* Boundary lemma for TopLevelVar when lookup_global returns Value.
     This is the only non-contradictory branch for StorageVarDecl + non-ArrayTV.
     After gvs with AllCaseEqs(), 3 goals remain:
       1) assign_subscripts INL + set_global INL + assign_result: success path
       2) assign_subscripts INL + set_global INR: TypeError from set_global
       3) assign_subscripts INR: error from assign_subscripts *)
  lookup_global cx src_id_opt (string_to_num id) st = (INL (Value v), st0) ==>
  value_has_type root_tv v ==>
  get_module_code cx src_id_opt = SOME code ==>
  env.type_defs = get_tenv cx ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  well_formed_type_value root_tv ==>
  assign_operation_runtime_typed env ty op ==>
  evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs)) ==>
  leaf_type root_tv (REVERSE sbs) <> NoneTV ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  all_tac >>
  rw[] >>
  gvs[Once assign_target_def, pairTheory.PAIR, AllCaseEqs(), bind_def, ignore_bind_def,
      lift_option_type_def, return_def, raise_def, lift_sum_def, type_check_def,
      assert_def, check_def, LET_THM, option_CASE_rator, var_decl_info_CASE_rator,
      prod_CASE_rator, type_value_CASE_rator, toplevel_value_CASE_rator,
      sum_CASE_rator] >-
  (* Goal 1: assign_subscripts INL + set_global INL + assign_result *)
  (metis_tac[assign_result_no_type_error_from_successful_assign_split]) >-
  (* Goal 2: set_global returns INR - derive value_has_type for v'' then close *)
  (`value_has_type root_tv v''` by metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
   simp[no_type_error_result_def] >> gen_tac >>
   spose_not_then strip_assume_tac >>
   (* Now: e = Error (TypeError msg), goal is F *)
   `set_global cx src_id_opt (string_to_num id) v'' s'' =
     (INR (Error (TypeError msg)),s'³')` by simp[] >>
   metis_tac[set_global_storage_no_type_error]) >-
  (* Goal 3: assign_subscripts returns INR *)
  (simp[no_type_error_result_def] >> gen_tac >>
   spose_not_then strip_assume_tac >>
   (* Now: e = TypeError msg, goal is F *)
   `assign_subscripts root_tv v (REVERSE sbs) op = INR (TypeError msg)` by simp[] >>
   metis_tac[assign_subscripts_no_type_error_runtime_typed])
QED

Theorem assign_target_TopLevelVar_Type_StorageVarDecl_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (Type t) ==>
  target_path_type env (Type t) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
  env.type_defs = get_tenv cx ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (StorageVarDecl is_transient typ, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  evaluate_type (get_tenv cx) typ = SOME root_tv ==>
  well_formed_type_value root_tv ==>
  (!elem_tv bd. root_tv <> ArrayTV elem_tv bd) ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  all_tac >> rpt strip_tac >>
  `well_formed_vtype env.type_defs (Type t)` by metis_tac[top_level_vtype_well_formed] >>
  `typ = t` by metis_tac[top_level_Type_storage_decl] >>
  fs[] >>
  `evaluate_type env.type_defs ty = SOME (leaf_type root_tv (REVERSE sbs))`
    by metis_tac[target_path_type_Type_evaluate_leaf] >>
  `leaf_type root_tv (REVERSE sbs) <> NoneTV`
    by metis_tac[assignable_type_evaluate_not_NoneTV, target_path_type_Type_evaluate_leaf_not_NoneTV] >>
  Cases_on `lookup_global cx src_id_opt (string_to_num id) st` >>
  Cases_on `q` >> gvs[] >-
  (* INL: toplevel_value *)
  (Cases_on `x` >> gvs[] >-
   (* Value v: apply boundary lemma via metis *)
   (metis_tac[assign_target_TopLevelVar_Value_branch_ntr, lookup_global_storage_Value_typed]) >-
   (* HashMapRef: contradiction *)
   (metis_tac[lookup_global_HashMapRef_not_StorageVarDecl]) >>
   (* ArrayRef: contradiction with non-ArrayTV root *)
   metis_tac[lookup_global_ArrayRef_not_StorageVarDecl]) >>
  (* INR: no TypeError possible for StorageVarDecl + non-ArrayTV *)
  imp_res_tac lookup_global_state >>
  gvs[] >>
  imp_res_tac assign_target_TopLevelVar_lookup_global_INR_propagate >>
  gvs[] >>
  CCONTR_TAC >>
  gvs[no_type_error_result_def, sumTheory.INR_11] >>
  metis_tac[lookup_global_StorageVarDecl_non_ArrayTV_no_TypeError]
QED

Theorem top_level_HashMapRef_assign_no_type_error:
  runtime_consistent env cx st ==>
  FLOOKUP env.toplevel_vtypes (src_id_opt,string_to_num id) = SOME (HashMapT kt vt) ==>
  target_path_type env (HashMapT kt vt) sbs (Type ty) ==>
  assignable_type (get_tenv cx) ty ==>
  assign_operation_runtime_typed env ty op ==>
  assign_operation_matches_target_shape (BaseTargetV (TopLevelVar src_id_opt id) sbs) op ==>
  assign_target_assignable (BaseTargetV (TopLevelVar src_id_opt id) sbs) st ==>
  well_formed_vtype (get_tenv cx) (HashMapT kt vt) ==>
  get_module_code cx src_id_opt = SOME code ==>
  find_var_decl_by_num (string_to_num id) code = SOME (HashMapVarDecl is_transient kt vt, id_str) ==>
  lookup_var_slot_from_layout cx is_transient src_id_opt id_str = SOME slot ==>
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) sbs) op st = (res, st') ==>
  no_type_error_result res
Proof
  cheat
QED
Resume assign_target_sound_mutual[sound_TopLevelVar]:
  cheat
QED

Resume assign_target_sound_mutual[sound_ImmutableVar]:
  cheat
QED

Resume assign_target_sound_mutual[sound_TupleTargetV]:
  cheat
QED

Resume assign_target_sound_mutual[sound_assign_targets_cons]:
  cheat
QED

Finalise assign_target_sound_mutual


Theorem assign_targets_preserves_runtime_consistent:
  runtime_consistent env cx st /\
  target_assignment_values_typed env cx st tgts gvs vs /\
  EVERY (\gv. assign_target_assignable_context cx gv st) gvs /\
  assign_targets cx gvs vs st = (INL res, st') ==>
  runtime_consistent env cx st'
Proof
  metis_tac[assign_target_preserves_state_well_typed_mutual]
QED

Theorem assign_target_preserves_runtime_consistent:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\ assign_target_assignable_context cx gv st /\
  assign_target cx gv op st = (INL res, st') ==>
  runtime_consistent env cx st'
Proof
  metis_tac[assign_target_preserves_state_well_typed_mutual]
QED

Theorem assign_targets_preserves_state_well_typed:
  runtime_consistent env cx st /\
  target_assignment_values_typed env cx st tgts gvs vs /\
  EVERY (\gv. assign_target_assignable_context cx gv st) gvs /\
  assign_targets cx gvs vs st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  metis_tac[assign_targets_preserves_runtime_consistent, runtime_consistent_def]
QED

Theorem assign_target_preserves_state_well_typed:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\ assign_target_assignable_context cx gv st /\
  assign_target cx gv op st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  metis_tac[assign_target_preserves_runtime_consistent, runtime_consistent_def]
QED

Theorem assign_target_preserves_runtime_consistent_result:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\ assign_target_assignable_context cx gv st /\
  assign_target cx gv op st = (res, st') ==>
  runtime_consistent env cx st'
Proof
  metis_tac[assign_target_preserves_state_well_typed_mutual]
QED

Theorem assign_target_preserves_state_well_typed_result:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\ assign_target_assignable_context cx gv st /\
  assign_target cx gv op st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  metis_tac[assign_target_preserves_runtime_consistent_result, runtime_consistent_def]
QED

Theorem materialise_preserves_type:
  state_well_typed st /\ toplevel_value_typed tvl tv /\ well_formed_type_value tv /\
  materialise cx tvl st = (INL v, st') ==>
  state_well_typed st' /\ value_has_type tv v
Proof
  rpt strip_tac >>
  drule materialise_state >> strip_tac >> gvs[] >>
  Cases_on `tvl` >>
  gvs[materialise_def, bind_def, return_def, raise_def,
      toplevel_value_typed_def, AllCaseEqs()] >>
  metis_tac[read_storage_slot_success_type, well_formed_type_value_def]
QED

Theorem get_Value_preserves_type:
  toplevel_value_typed (Value v) tv ==> value_has_type tv v
Proof
  simp[toplevel_value_typed_def]
QED

(* eval_for preservation depends on statement-list soundness and therefore lives
   in vyperTypeStmtSoundnessScript.sml to avoid a StatePreservation ->
   StmtSoundness -> StatePreservation cycle. *)
