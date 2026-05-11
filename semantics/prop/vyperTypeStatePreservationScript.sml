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
  vyperScopePreservation vyperImmutablesPreservation
  vyperStatePreservation vyperTypeEnv vyperTypeABI vyperTypeBuiltins vyperTypeExprSoundness
Libs
  wordsLib

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

Theorem set_immutable_preserves_state_well_typed:
  state_well_typed st /\ value_has_type tv v /\ well_formed_type_value tv /\
  set_immutable cx src n tv v st = (INL res, st') ==>
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

Theorem assign_target_preserves_state_well_typed_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (INL res, st') ==>
    !env tgt ty.
      runtime_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op ==>
      runtime_consistent env cx st') /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (INL res, st') ==>
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
  rename1 `assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (INL res, st')` >>
  `?vt final_tv. location_runtime_typed env cx st (ScopedVar id) vt /\
                 target_path_type env vt sbs (Type ty) /\
                 place_leaf_typed env vt sbs ty final_tv` by
    metis_tac[target_runtime_typed_place_leaf_typed] >>
  gvs[location_runtime_typed_def] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  qpat_x_assum `(case find_containing_scope (string_to_num id) sc of _ => _) _ = _` mp_tac >>
  Cases_on `find_containing_scope (string_to_num id) sc` >> gvs[return_def, raise_def] >>
  PairCases_on `x` >> gvs[] >> strip_tac >> gvs[] >>
  `sc = st.scopes` by gvs[get_scopes_def, return_def] >> gvs[] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `do _ od _ = (INL res,st')` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def,
       lift_sum_def, type_check_def, assert_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(case assign_subscripts entry.type entry.value (REVERSE sbs) op of _ => _) _ = _` mp_tac >>
  Cases_on `assign_subscripts entry.type entry.value (REVERSE sbs) op` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  rename1 `assign_subscripts entry.type entry.value (REVERSE sbs) op = INL new_value` >>
  sg `value_has_type entry.type new_value` >- (
    gvs[place_leaf_typed_def, place_leaf_path_typed_def] >>
    irule assign_subscripts_preserves_type >> simp[] >>
    conj_asm1_tac >- (
      drule evaluate_type_well_formed_type_value >> rw[] ) >>
    goal_assum $ drule_at Any >>
    conj_tac >- metis_tac[assign_operation_leaf_type_update] >>
    conj_tac >- metis_tac[assign_operation_leaf_type_append] >>
    conj_tac >- metis_tac[assign_operation_leaf_type_replace] >>
    gvs[runtime_consistent_def] >>
    drule_all lookup_scopes_state_well_typed_value_has_type >> simp[]
  ) >>
  drule find_containing_scope_structure >> strip_tac >> gvs[] >>
  drule find_containing_scope_pre_none >> strip_tac >> gvs[] >>
  qpat_x_assum `set_scopes _ _ = _` mp_tac >>
  simp[set_scopes_def, return_def, raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_result _ _ _ _ _ = (INL res,st')`
    (ASSUME_TAC o MATCH_MP assign_result_preserves_state) >>
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
  rename1 `assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st')` >>
  `?vt final_tv. location_runtime_typed env cx st (TopLevelVar src id) vt /\
                 target_path_type env vt sbs (Type ty) /\
                 place_leaf_typed env vt sbs ty final_tv` by
    metis_tac[target_runtime_typed_place_leaf_typed] >>
  gvs[location_runtime_typed_def] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  Cases_on `tv` >> gvs[]
  >- (
    gvs[bind_def, return_def, raise_def, lift_option_type_def,
        lift_sum_def, ignore_bind_def, AllCaseEqs()] >>
    imp_res_tac assign_result_preserves_state >> gvs[] >>
    imp_res_tac lookup_global_state >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    qpat_x_assum `(case assign_subscripts _ _ _ _ of _ => _) _ = _` mp_tac >>
    Cases_on `assign_subscripts var_tv v (REVERSE sbs) op` >>
    gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
    qpat_x_assum `(case OPTION_BIND _ _ of _ => _) _ = _` mp_tac >>
    Cases_on `OPTION_BIND (find_var_decl_by_num (string_to_num id) ts)
          (λp. case FST p of StorageVarDecl v5 typ => evaluate_type (get_tenv cx) typ
               | HashMapVarDecl v7 v8 v9 => NONE)` >>
    gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
    qpat_x_assum `(case get_module_code _ _ of _ => _) _ = _` mp_tac >>
    Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
    strip_tac >> gvs[] >>
    gvs[runtime_consistent_def] >>
    conj_tac >- (
      irule set_global_preserves_env_consistent >> goal_assum drule >> simp[]) >>
    conj_tac >- (
      qspecl_then [`cx`, `src`, `string_to_num id`, `v'³'`, `s''`, `INL ()`, `s'⁶'`, `env`]
        mp_tac set_global_preserves_state_well_typed >> simp[]) >>
    qspecl_then [`cx`, `src`, `string_to_num id`, `v'³'`, `s''`, `INL ()`, `s'⁶'`]
      mp_tac set_global_preserves_accounts_well_typed >> simp[])
  >- (
    gvs[bind_def, return_def, raise_def, lift_option_type_def,
        lift_sum_def, ignore_bind_def, AllCaseEqs()] >>
    PairCases_on `x` >> gvs[] >>
    imp_res_tac assign_result_preserves_state >> gvs[] >>
    imp_res_tac lookup_global_state >>
    imp_res_tac lift_option_type_state >>
    imp_res_tac read_storage_slot_state >> gvs[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    Cases_on `split_hashmap_subscripts v x1` >>
    gvs[bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def] >>
    PairCases_on `x` >> gvs[bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def] >>
    Cases_on `compute_hashmap_slot c (t::x1') (x0::TAKE (LENGTH x1 - LENGTH x2) x1)` >>
    gvs[bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def] >>
    Cases_on `evaluate_type (get_tenv cx) x0'` >>
    gvs[bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def] >>
    Cases_on `read_storage_slot cx b x x' s'⁴'` >> Cases_on `q` >> gvs[] >>
    Cases_on `assign_subscripts x' x'' x2 op` >>
    gvs[bind_def, return_def, raise_def, lift_option_type_def, lift_sum_def] >>
    Cases_on `write_storage_slot cx b x x' x''' r` >> Cases_on `q` >> gvs[] >>
    strip_tac >> gvs[] >>
    imp_res_tac assign_result_preserves_state >> gvs[] >>
    imp_res_tac lookup_global_state >>
    qpat_x_assum `(case get_module_code _ _ of _ => _) _ = _` mp_tac >>
    Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
    qpat_x_assum `(case case REVERSE _ of _ => _ | _ => _ of _ => _) _ = _` mp_tac >>
    Cases_on `REVERSE sbs` >> gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
    imp_res_tac read_storage_slot_preserves_env_consistent >>
    imp_res_tac read_storage_slot_preserves_state_well_typed >>
    imp_res_tac read_storage_slot_state >> gvs[] >>
    gvs[runtime_consistent_def] >>
    conj_tac >- (
      irule write_storage_slot_preserves_env_consistent >>
      goal_assum drule >> simp[]) >>
    conj_tac >- (
      qspecl_then [`cx`, `b`, `x`, `x'`, `x'³'`, `r`, `INL ()`, `r''`]
        mp_tac write_storage_slot_preserves_state_well_typed_any >> simp[]) >>
    qspecl_then [`cx`, `b`, `x`, `x'`, `x'³'`, `r`, `INL ()`, `r''`]
      mp_tac write_storage_slot_preserves_accounts_well_typed >> simp[])
  >>
    gvs[bind_def, return_def, raise_def, lift_option_type_def,
        lift_sum_def, ignore_bind_def, assert_def, check_def, AllCaseEqs()] >>
    pairarg_tac >>
    gvs[option_CASE_rator, AllCaseEqs(), raise_def, return_def,
        type_value_CASE_rator, bind_apply, sum_CASE_rator,
        bound_CASE_rator, assign_operation_CASE_rator, assert_def] >>
    imp_res_tac assign_result_preserves_state >> gvs[] >>
    imp_res_tac lookup_global_state >>
    imp_res_tac resolve_array_element_state >>
    imp_res_tac read_storage_slot_state >>
    imp_res_tac get_storage_backend_state >> gvs[]
    >> TRY (
      qmatch_rename_tac`runtime_consistent env cx sg` >>
      qmatch_assum_rename_tac`write_storage_slot _ _ _ _ _ sf = (_,sg)` >>
      qmatch_assum_rename_tac`write_storage_slot _ _ _ _ _ se = (_,sf)` >>
      `(runtime_consistent env cx sf ⇒ runtime_consistent env cx sg) ∧
       runtime_consistent env cx sf` suffices_by (rw[] >> gvs[]) >>
      rpt strip_tac) >>
    qmatch_rename_tac`runtime_consistent _ _ sk` >>
    qpat_x_assum`write_storage_slot _ _ _ _ _ _ = (_,sk)`assume_tac >>
    drule write_storage_slot_preserves_env_consistent >>
    drule write_storage_slot_preserves_state_well_typed_any >>
    drule write_storage_slot_preserves_accounts_well_typed >>
    gvs[runtime_consistent_def]
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
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  drule_at(Pat`set_immutable`) set_immutable_preserves_state_well_typed >>
  simp[] >>
  impl_keep_tac >- (
    gvs[place_leaf_typed_def, place_leaf_path_typed_def] >>
    qspecl_then [`tv`, `v`, `REVERSE is`, `op`, `a'`] mp_tac
      assign_subscripts_preserves_type >>
    simp[] >>
    impl_tac >- (
      conj_tac >- metis_tac[assign_operation_leaf_type_replace] >>
      conj_tac >- metis_tac[assign_operation_leaf_type_update] >>
      metis_tac[assign_operation_leaf_type_append]) >>
    simp[]) >>
  qpat_x_assum `assign_result _ _ _ _ _ = (INL res,st')`
    (ASSUME_TAC o MATCH_MP assign_result_preserves_state) >>
  strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[set_immutable_def, get_address_immutables_def, bind_def, lift_option_def,
       set_address_immutables_def, return_def, raise_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(case ALOOKUP _ _ of NONE => _ | SOME _ => _) _ = _` mp_tac >>
  Cases_on `ALOOKUP s''.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  gvs[env_consistent_def] >>
  `current_module cx = env.current_src` by (
    gvs[env_context_consistent_def] ) >>
  conj_tac >- (
    gvs[env_scopes_consistent_def] >>
    metis_tac[] ) >>
  gvs[env_immutables_consistent_def, FLOOKUP_UPDATE] >>
  conj_tac >- ( rw[] ) >>
  conj_tac >- ( rw[] >> gvs[env_context_consistent_def] >>
    first_x_assum irule >> goal_assum drule >> simp[]
  ) >>
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

Resume assign_target_preserves_state_well_typed_mutual[TupleTargetV]:
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  Cases_on `tgt` >> gvs[target_runtime_typed_def, target_value_shape_def, well_typed_atarget_def,
      target_assignment_values_typed_def] >>
  rename1 `assign_targets cx gvs vs st = (INL res,st')` >>
  qpat_x_assum `!st0 st1. assign_targets cx gvs vs st0 = (INL res,st1) ==> _`
    (qspecl_then [`st`, `st'`] mp_tac) >>
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
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(), target_assignment_values_typed_def] >>
  Cases_on `tgts` >> gvs[LIST_REL3_def] >>
  rename1 `assign_target cx gv (Replace v) st = (INL head_res, s_mid)` >>
  rename1 `assign_targets cx gvs vs s_mid = (INL _, st')` >>
  `runtime_consistent env cx s_mid` by (
    qpat_x_assum `!st0 res0 st1. assign_target cx gv (Replace v) st0 = (INL res0,st1) ==> _`
      (qspecl_then [`st`, `head_res`, `s_mid`] mp_tac) >>
    simp[] >>
    disch_then (qspecl_then [`env`, `h`, `ty`] mp_tac) >>
    simp[assign_operation_runtime_typed_def, value_runtime_typed_def]) >>
  qpat_x_assum `!st0 st1. assign_targets cx gvs vs st0 = (INL (),st1) ==> _`
    (qspecl_then [`s_mid`, `st'`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`env`, `t`] mp_tac) >>
  simp[target_assignment_values_typed_def] >>
  strip_tac >>
  first_x_assum irule >>
  `target_assignment_values_typed env cx st t gvs vs` by
    simp[target_assignment_values_typed_def] >>
  drule_all target_assignment_values_typed_rebuild >>
  simp[target_assignment_values_typed_def]
QED

Finalise assign_target_preserves_state_well_typed_mutual

Theorem assign_targets_preserves_runtime_consistent:
  runtime_consistent env cx st /\
  target_assignment_values_typed env cx st tgts gvs vs /\
  assign_targets cx gvs vs st = (INL res, st') ==>
  runtime_consistent env cx st'
Proof
  metis_tac[assign_target_preserves_state_well_typed_mutual]
QED

Theorem assign_target_preserves_runtime_consistent:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_target cx gv op st = (INL res, st') ==>
  runtime_consistent env cx st'
Proof
  metis_tac[assign_target_preserves_state_well_typed_mutual]
QED

Theorem assign_targets_preserves_state_well_typed:
  runtime_consistent env cx st /\
  target_assignment_values_typed env cx st tgts gvs vs /\
  assign_targets cx gvs vs st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  metis_tac[assign_targets_preserves_runtime_consistent, runtime_consistent_def]
QED

Theorem assign_target_preserves_state_well_typed:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_target cx gv op st = (INL res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  metis_tac[assign_target_preserves_runtime_consistent, runtime_consistent_def]
QED

(* TEMPORARILY CHEATED - statement soundness needs preservation for both
   success and exception/error results of assignment.  This is the all-result
   version of the success-only assignment preservation theorem above. *)
Theorem assign_target_preserves_runtime_consistent_result:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
  assign_target cx gv op st = (res, st') ==>
  runtime_consistent env cx st'
Proof
  cheat
QED

Theorem assign_target_preserves_state_well_typed_result:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\ assign_operation_runtime_typed env ty op /\
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
