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

Resume assign_target_sound_mutual[sound_TopLevelVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    drule (cj 1 assign_target_preserves_state_well_typed_mutual) >>
    disch_then (qspecl_then [`env`, `tgt`, `ty`] mp_tac) >>
    simp[]) >>
  reverse $ gvs[assign_target_def, bind_apply, AllCaseEqs()]
  >- (
    rw[no_type_error_result_def] >> rpt strip_tac >> gvs[] >>
    drule lookup_global_top_level_assignable_no_type_error >>
    disch_then drule >> rw[] )
  >- (
    drule_at Any lookup_global_success_get_module_code >>
    strip_tac >> gvs[lift_option_type_def,return_def] ) >>
  gvs[lift_option_type_def,return_def,AllCaseEqs(),
      raise_def,option_CASE_rator] >>
  Cases_on`tv` >- (
    gvs[assign_target_assignable_context_def] >>
    drule_then drule lookup_global_Value_not_HashMapVarDecl >>
    disch_then drule >> simp[] >> strip_tac >>
    PairCases_on`p` >> Cases_on`p0` >> gvs[IS_SOME_EXISTS] >>
    reverse(gvs[bind_apply,AllCaseEqs(),return_def]) >- (
      gvs[lift_sum_def, sum_CASE_rator, AllCaseEqs(),
          return_def, raise_def, no_type_error_result_def] >>
      rpt strip_tac >> gvs[] >>
      funpow 3 drule_then drule
        top_level_storage_value_assign_subscripts_no_type_error >>
      simp[] >>
      imp_res_tac lookup_global_state ) >>
    reverse $ gvs[ignore_bind_apply, AllCaseEqs(),
                  no_type_error_result_def] >- (
      rpt strip_tac >> gvs[] >>
      funpow 2 drule_then drule
        top_level_storage_value_assign_success_no_type_error >>
      simp[] >>
      imp_res_tac lookup_global_state >>
      gvs[lift_sum_def, sum_CASE_rator, AllCaseEqs(),
          raise_def, return_def]
    ) >>
    rpt strip_tac >> gvs[] >>
    drule_at Any assign_result_no_type_error_from_successful_assign >>
    simp[no_type_error_result_def] >>
    gvs[lift_sum_def, sum_CASE_rator, AllCaseEqs(),
        raise_def, return_def] 
  ) >>
  gvs[]
  >- cheat (* HashMapRef case *)
  >> cheat (* ArrayRef case *)
QED

Resume assign_target_sound_mutual[sound_ImmutableVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    irule (cj 1 assign_target_preserves_state_well_typed_mutual) >>
    goal_assum drule_all >> simp[]) >>
  cheat
QED

Resume assign_target_sound_mutual[sound_TupleTargetV]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    irule (cj 1 assign_target_preserves_state_well_typed_mutual) >>
    goal_assum drule_all >> simp[]) >>
  cheat
QED

Resume assign_target_sound_mutual[sound_assign_targets_cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[assign_target_def] >>
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
