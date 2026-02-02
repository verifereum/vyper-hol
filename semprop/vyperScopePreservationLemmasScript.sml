Theory vyperScopePreservationLemmas

Ancestors
  vyperInterpreter vyperLookup

(* ===== Lemmas about scopes preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_scopes:
  !x st res st'. return x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[return_def]
QED

Theorem raise_scopes:
  !e st res st'. raise e st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[raise_def]
QED

Theorem get_scopes_scopes:
  ∀st res st'. get_scopes st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_scopes_def, return_def]
QED

Theorem check_scopes:
  !b s st res st'. check b s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[check_def, assert_def]
QED

Theorem lift_option_scopes:
  !x s st res st'. lift_option x s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_scopes:
  !x st res st'. lift_sum x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_scopes:
  !tv st res st'. get_Value tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_scopes_id:
  !st res st'. get_scopes st = (res, st') ==> st' = st
Proof
  rw[get_scopes_def, return_def]
QED

Theorem get_accounts_scopes:
  !st res st'. get_accounts st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_address_immutables_scopes:
  !cx st res st'. get_address_immutables cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem set_address_immutables_scopes:
  !cx imms st res st'. set_address_immutables cx imms st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_address_immutables_def, return_def] >> simp[]
QED

Theorem get_transient_storage_scopes:
  !st res st'. get_transient_storage st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_transient_storage_def, return_def]
QED

Theorem update_transient_scopes:
  !f st res st'. update_transient f st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[update_transient_def, return_def] >> simp[]
QED

Theorem update_accounts_scopes:
  !f st res st'. update_accounts f st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[update_accounts_def, return_def] >> simp[]
QED

Theorem get_storage_backend_scopes:
  !cx is_trans st res st'. get_storage_backend cx is_trans st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[get_storage_backend_def, bind_def, get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem set_storage_backend_scopes:
  !cx is_trans storage' st res st'. set_storage_backend cx is_trans storage' st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[set_storage_backend_def, bind_def, update_transient_def, get_accounts_def,
     update_accounts_def, return_def] >> simp[]
QED

Theorem read_storage_slot_scopes:
  !cx is_trans slot tv st res st'. read_storage_slot cx is_trans slot tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

Theorem write_storage_slot_scopes:
  !cx is_trans slot tv v st res st'. write_storage_slot cx is_trans slot tv v st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[write_storage_slot_def, bind_def, ignore_bind_def, lift_option_def,
     get_storage_backend_def, set_storage_backend_def,
     get_transient_storage_def, update_transient_def,
     get_accounts_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `encode_value tv v` >> gvs[return_def, raise_def]
QED

(* ===== Lemmas about immutables preservation ===== *)

(* Storage operations preserve immutables *)
Theorem read_storage_slot_immutables:
  !cx is_trans slot tv st res st'. 
    read_storage_slot cx is_trans slot tv st = (res, st') ==> 
    st'.immutables = st.immutables
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

Theorem write_storage_slot_immutables:
  !cx is_trans slot tv v st res st'. 
    write_storage_slot cx is_trans slot tv v st = (res, st') ==> 
    st'.immutables = st.immutables
Proof
  Cases_on `is_trans` >>
  rw[write_storage_slot_def, bind_def, ignore_bind_def, lift_option_def,
     get_storage_backend_def, set_storage_backend_def,
     get_transient_storage_def, update_transient_def,
     get_accounts_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `encode_value tv v` >> gvs[return_def, raise_def]
QED

Theorem lookup_global_immutables:
  !cx src n st res st'. 
    lookup_global cx src n st = (res, st') ==> 
    st'.immutables = st.immutables
Proof
  rw[lookup_global_def, bind_def, return_def, lift_option_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[bind_def, return_def, raise_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt CASE_TAC >> gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_immutables >> simp[]
QED

Theorem set_global_immutables:
  !cx src n v st res st'. 
    set_global cx src n v st = (res, st') ==> 
    st'.immutables = st.immutables
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `lookup_var_slot_from_layout cx b n` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (type_env x) t` >> gvs[return_def, raise_def] >>
  imp_res_tac write_storage_slot_immutables >> gvs[]
QED

Theorem get_immutables_scopes:
  !cx src st res st'. get_immutables cx src st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_immutables_def, bind_def, return_def, get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_scopes:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lookup_global_def, bind_def, return_def, lift_option_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[bind_def, return_def, raise_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt CASE_TAC >> gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  drule read_storage_slot_scopes >> simp[]
QED

Theorem set_global_scopes:
  !cx src n v st res st'. set_global cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[return_def, raise_def, bind_def] >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  Cases_on `lookup_var_slot_from_layout cx b n` >> gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (type_env x) t` >> gvs[return_def, raise_def] >>
  imp_res_tac write_storage_slot_scopes >> gvs[]
QED

Theorem set_immutable_scopes:
  !cx src n v st res st'. set_immutable cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_immutable_def, bind_def, return_def, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem push_log_scopes:
  !l st res st'. push_log l st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[push_log_def, return_def] >> simp[]
QED

Theorem transfer_value_scopes:
  !f t a st res st'. transfer_value f t a st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def, check_def, assert_def, update_accounts_def] >>
  gvs[raise_def] >> simp[]
QED

Theorem lookup_flag_mem_scopes:
  !cx nsid mid st res st'. lookup_flag_mem cx nsid mid st = (res, st') ==> st'.scopes = st.scopes
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

(* switch_BoolV preserves scopes if both branches preserve scopes. *)
Theorem switch_BoolV_scopes:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ⇒
    st'.scopes = st.scopes
Proof
  rw[switch_BoolV_def, raise_def]
QED

Theorem finally_pop_function_scopes:
  ∀f prev st res st'.
    finally f (pop_function prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[pop_function_def, finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem finally_set_scopes:
  ∀f prev st res st'.
    finally f (set_scopes prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem find_containing_scope_map_fdom:
  ∀id sc pre env v rest a'.
    find_containing_scope id sc = SOME (pre, env, v, rest) ⇒
    MAP FDOM (pre ++ env |+ (id, a') :: rest) = MAP FDOM sc
Proof
  rpt strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  gvs[] >>
  `id IN FDOM env` by gvs[finite_mapTheory.FLOOKUP_DEF] >>
  gvs[pred_setTheory.ABSORPTION_RWT]
QED

Theorem assign_target_preserves_scopes_dom:
  (∀cx gv ao st res st'. assign_target cx gv ao st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes) ∧
  (∀cx gvs vs st res st'. assign_targets cx gvs vs st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes)
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar case *)
  >- (strip_tac >> gvs[assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
      Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
      PairCases_on `x` >> gvs[bind_def, lift_sum_def] >>
      Cases_on `assign_subscripts x2 (REVERSE is) ao` >>
      gvs[return_def, raise_def, bind_def, ignore_bind_def, set_scopes_def] >>
      drule find_containing_scope_map_fdom >> simp[])
  (* TopLevelVar case - now uses storage operations *)
  >- (strip_tac >> gvs[assign_target_def, bind_def, lift_option_def] >>
      Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]
      (* NONE case: lookup_global still runs, then error *)
      >- (qpat_x_assum `_ = (res, st')` mp_tac >>
          rpt CASE_TAC >> gvs[return_def, raise_def] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lookup_global_scopes >> gvs[])
      (* SOME case: main execution path *)
      >> (qpat_x_assum `_ = (res, st')` mp_tac >>
          simp[return_def] >> rpt CASE_TAC >> 
          gvs[return_def, raise_def, lift_sum_def, bind_def, ignore_bind_def] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lookup_global_scopes >> gvs[] >>
          (* Value case: use set_global_scopes *)
          TRY (qpat_x_assum `_ = (res, st')` mp_tac >>
               rpt CASE_TAC >> gvs[return_def, raise_def] >>
               rpt strip_tac >> gvs[] >>
               imp_res_tac set_global_scopes >> gvs[]) >>
          (* HashMapRef case: decompose tuple, use read/write_storage_slot_scopes *)
          TRY (PairCases_on `x'` >> gvs[bind_def] >>
               qpat_x_assum `_ = (res, st')` mp_tac >>
               rpt CASE_TAC >> gvs[return_def, raise_def] >>
               rpt strip_tac >> gvs[] >>
               imp_res_tac read_storage_slot_scopes >> 
               imp_res_tac write_storage_slot_scopes >> gvs[])))
  (* ImmutableVar case *)
  >- (strip_tac >> gvs[assign_target_def, bind_def] >>
      Cases_on `get_immutables cx NONE st` >> gvs[] >>
      drule get_immutables_scopes >> strip_tac >>
      Cases_on `q` >> gvs[] >>
      gvs[lift_option_def, AllCaseEqs(), return_def, raise_def]
      >- (imp_res_tac lift_sum_scopes >> gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def]
          >- (imp_res_tac set_immutable_scopes >> gvs[] >>
              Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def])
          >- (imp_res_tac set_immutable_scopes >> gvs[] >>
              Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def]))
      >- (imp_res_tac lift_sum_scopes >> gvs[] >>
          Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def])
      >- (Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def]))
  (* TupleTargetV with TupleV - uses IH *)
  >- (rpt strip_tac >>
      gvs[assign_target_def, bind_def, check_def, assert_def, return_def, raise_def,
          ignore_bind_def, AllCaseEqs()])
  (* TupleTargetV error cases - all just raise *)
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  (* assign_targets [] [] *)
  >- simp[assign_target_def, return_def]
  (* assign_targets cons case - uses IH *)
  >- (rpt strip_tac >>
      gvs[assign_target_def, bind_def, AllCaseEqs(), return_def, get_Value_def] >>
      res_tac >> imp_res_tac get_Value_scopes >> gvs[] >> TRY (first_x_assum drule >> simp[]))
  (* assign_targets length mismatch cases *)
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
QED

Theorem assign_target_preserves_scopes_dom_lookup:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes)))
Proof
  conj_tac >> rpt strip_tac >-
  (drule (CONJUNCT1 assign_target_preserves_scopes_dom) >> strip_tac >>
   metis_tac[lookup_scopes_dom_iff]) >>
  drule (CONJUNCT2 assign_target_preserves_scopes_dom) >> strip_tac >>
  metis_tac[lookup_scopes_dom_iff]
QED

Theorem new_variable_scope_property:
  ∀id v st res st'.
    new_variable id v st = (res, st') ∧ st.scopes ≠ [] ⇒
    st'.scopes ≠ [] ∧
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    TL st'.scopes = TL st.scopes
Proof
  rpt strip_tac >> Cases_on `st.scopes` >> gvs[] >>
  gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def,
      assert_def, set_scopes_def, AllCaseEqs(), raise_def, ignore_bind_def] >>
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem push_scope_creates_empty_hd:
  ∀st res st'.
    push_scope st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_def, return_def] >> simp[]
QED

Theorem push_scope_with_var_creates_singleton_hd:
  ∀nm v st res st'.
    push_scope_with_var nm v st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY |+ (nm, v) ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_with_var_def, return_def] >> simp[]
QED

Theorem finally_pop_scope_preserves_tl_dom:
  ∀body st res st'.
    finally body pop_scope st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)
Proof
  rpt strip_tac >>
  gvs[finally_def, AllCaseEqs()] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def] >>
  first_x_assum drule >> simp[]
QED

Theorem push_scope_finally_pop_preserves_dom:
  ∀body st res st'.
    do push_scope; finally body pop_scope od st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt strip_tac >>
  gvs[push_scope_def, bind_def, ignore_bind_def, return_def] >>
  gvs[finally_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem finally_set_scopes_dom:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED
