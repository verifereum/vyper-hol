(*
 * State-update preservation lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeStatePreservation
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperStorageBackend vyperLookup vyperEncodeDecode vyperArith vyperAssignPreservesType
  vyperTypeSystem vyperTypeValues
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
  >- (first_x_assum irule >> gvs[EVERY_MEM])
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

Theorem place_leaf_typed_evaluate_type:
  place_leaf_typed env vt sbs ty final_tv ==> evaluate_type env.type_defs ty = SOME final_tv
Proof
  MAP_EVERY qid_spec_tac [`vt`, `sbs`] >>
  Induct_on `sbs` >> Cases_on `vt` >> rw[place_leaf_typed_def] >> gvs[] >>
  metis_tac[]
QED

Theorem assign_operation_leaf_replace:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (Replace v) ==>
  value_has_type final_tv v
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
  drule place_leaf_typed_evaluate_type >> strip_tac >> gvs[]
QED

Theorem assign_operation_leaf_append:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (AppendOp v) ==>
  ?elem_tv n. final_tv = ArrayTV elem_tv (Dynamic n) /\ value_has_type elem_tv v
Proof
  rw[assign_operation_runtime_typed_def] >>
  drule place_leaf_typed_evaluate_type >> strip_tac >> gvs[evaluate_type_def]
QED

Theorem assign_operation_leaf_update:
  place_leaf_typed env vt sbs ty final_tv /\
  assign_operation_runtime_typed env ty (Update upd_ty bop nv) /\
  value_has_type final_tv la /\
  assign_subscripts final_tv la [] (Update upd_ty bop nv) = INL lv ==>
  value_has_type final_tv lv
Proof
  rw[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
  drule place_leaf_typed_evaluate_type >> strip_tac >> gvs[] >>
  gvs[Once assign_subscripts_def, LET_THM] >>
  irule well_typed_binop_success_type >>
  qexists_tac `bop` >> qexists_tac `ty` >> qexists_tac `rhs_ty` >>
  qexists_tac `env.type_defs` >> qexists_tac `final_tv` >> qexists_tac `tv` >>
  qexists_tac `ty` >> qexists_tac `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u` >>
  qexists_tac `la` >> qexists_tac `nv` >>
  simp[]
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
  simp[target_runtime_typed_def]
QED

Theorem target_runtime_typed_rebuild:
  runtime_consistent env cx st' /\ target_runtime_typed env cx st tgt ty gv ==>
  target_runtime_typed env cx st' tgt ty gv
Proof
  Cases_on `gv` >> simp[target_runtime_typed_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `l` >> gvs[location_runtime_typed_def, runtime_consistent_def, env_consistent_def]
  >- (
    rename1 `FLOOKUP env.var_types (string_to_num s) = SOME var_ty` >>
    `?entry'. lookup_scopes (string_to_num s) st'.scopes = SOME entry'` by metis_tac[IS_SOME_EXISTS] >>
    `entry'.type = entry.type` by metis_tac[optionTheory.SOME_11] >>
    qexists_tac `Type var_ty` >> simp[] >>
    qexists_tac `final_tv` >> simp[])
  >- (
    rename1 `FLOOKUP env.bare_globals (current_module cx,string_to_num s) = SOME imm_ty` >>
    `?pair. FLOOKUP (get_source_immutables (current_module cx)
        (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m))
        (string_to_num s) = SOME pair` by metis_tac[IS_SOME_EXISTS] >>
    PairCases_on `pair` >>
    `pair0 = tv` by metis_tac[optionTheory.SOME_11] >>
    qexists_tac `Type imm_ty` >> simp[] >>
    qexists_tac `final_tv` >> simp[] >>
    qexists_tac `get_source_immutables (current_module cx)
        (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m)` >>
    qexists_tac `pair1` >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
    Cases_on `ALOOKUP x (current_module cx)` >>
    gvs[get_immutables_def, get_address_immutables_def, bind_def, return_def,
        lift_option_def, get_source_immutables_def, AllCaseEqs()]) >>
  metis_tac[]
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
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  cheat
QED

Resume assign_target_preserves_state_well_typed_mutual[TopLevelVar]:
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  cheat
QED

Resume assign_target_preserves_state_well_typed_mutual[ImmutableVar]:
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  cheat
QED

Resume assign_target_preserves_state_well_typed_mutual[TupleTargetV]:
  rpt strip_tac >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs()] >>
  cheat
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
