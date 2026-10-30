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




(* eval_for preservation depends on statement-list soundness and therefore lives
   in vyperTypeStmtSoundnessScript.sml to avoid a StatePreservation ->
   StmtSoundness -> StatePreservation cycle. *)



(* Weak wrappers without shape/context premises - derived directly from the
   mutual theorem.  C5 statement branches that only need preservation can use
   these without deriving assign_operation_matches_target_shape or
   assign_target_assignable_context. *)
