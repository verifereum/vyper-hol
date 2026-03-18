Theory vyperUpdateTarget
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter vyperLookup vyperLookupStorage vyperAssignTarget

Definition update_target_def:
  update_target cx st av ao = SND (assign_target cx av ao st)
End

Definition valid_target_def:
  valid_target cx st av ao = ISL (FST (assign_target cx av ao st))
End

Theorem update_target_name_replace:
  ∀cx st n v.
    var_in_scope st n ⇒
    update_target cx st (BaseTargetV (ScopedVar n) []) (Replace v) =
    update_name st n v
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_name_replace >>
  pop_assum (qspecl_then [`v`, `cx`] strip_assume_tac) >>
  simp[]
QED

Theorem update_target_name_update:
  ∀cx st n ty bop v1 v2 v.
    evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                   NoneTV bop v1 v2 = INL v ∧
    lookup_name st n = SOME v1 ⇒
    update_target cx st (BaseTargetV (ScopedVar n) []) (Update ty bop v2) =
    update_name st n v
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_name_update >> simp[]
QED

Theorem valid_target_name_implies_var_in_scope:
  ∀cx st n ao. valid_target cx st (BaseTargetV (ScopedVar n) []) ao ⇒ var_in_scope st n
Proof
  rw[valid_target_def] >>
  metis_tac[assign_target_scoped_var_implies_var_in_scope]
QED

Theorem valid_target_name_replace:
  ∀cx st n v. var_in_scope st n ⇒ valid_target cx st (BaseTargetV (ScopedVar n) []) (Replace v)
Proof
  rw[valid_target_def] >>
  imp_res_tac assign_target_name_replace >> simp[]
QED

Theorem valid_target_name_update:
  ∀cx st n ty bop v1 v2 v.
    lookup_name st n = SOME v1 ∧
    evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                   NoneTV bop v1 v2 = INL v ⇒
    valid_target cx st (BaseTargetV (ScopedVar n) []) (Update ty bop v2)
Proof
  rw[valid_target_def] >>
  drule_all assign_target_name_update >> strip_tac >> simp[]
QED

Theorem update_target_name_subscripts:
  ∀cx st n sbs ao tv a a'.
    lookup_name_typed st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    update_target cx st (BaseTargetV (ScopedVar n) sbs) ao = update_name st n a'
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_name_subscripts_state >> simp[]
QED

Theorem valid_target_name_subscripts:
  ∀cx st n sbs ao tv a a'.
    lookup_name_typed st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    valid_target cx st (BaseTargetV (ScopedVar n) sbs) ao
Proof
  rw[valid_target_def] >>
  imp_res_tac assign_target_name_subscripts_valid >> simp[]
QED

Theorem update_target_preserves_toplevel_name_targets:
  ∀cx st av ao n.
    lookup_toplevel_name_target cx (update_target cx st av ao) n = lookup_toplevel_name_target cx st n
Proof
  simp[lookup_toplevel_name_target_def, lookup_base_target_def] >>
  rpt gen_tac >> Cases_on `n` >>
  simp[Once evaluate_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

Theorem update_target_preserves_name_targets:
  ∀cx st av ao n.
    valid_target cx st av ao ⇒
    lookup_name_target cx (update_target cx st av ao) n = lookup_name_target cx st n
Proof
  rw[valid_target_def, lookup_name_target_def,
     lookup_base_target_def, update_target_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  `MAP FDOM r.scopes = MAP FDOM st.scopes`
    by (drule (CONJUNCT1 vyperScopePreservationTheory.assign_target_preserves_scopes_dom) >> simp[]) >>
  `IS_SOME (lookup_scopes (string_to_num n) r.scopes) = IS_SOME (lookup_scopes (string_to_num n) st.scopes)`
    by (simp[GSYM var_in_scope_iff_lookup_name_typed, GSYM lookup_name_typed_def] >>
        irule var_in_scope_dom_iff >> simp[]) >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >-
  (* NONE case: no immutables for this target *)
  (`ALOOKUP r.immutables cx.txn.target = NONE`
     by (CCONTR_TAC >> gvs[] >>
         Cases_on `ALOOKUP r.immutables cx.txn.target` >> gvs[] >>
         drule assign_target_preserves_immutables_addr_dom_rev >> simp[]) >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def, lift_sum_def, LET_THM,
        get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
        option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
   CONV_TAC (RHS_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, bind_def, get_scopes_def,
        return_def, lift_sum_def, LET_THM, get_immutables_def, get_address_immutables_def,
        lift_option_def, lift_option_type_def,
        option_CASE_rator, sum_CASE_rator, prod_CASE_rator])) >>
   Cases_on `cx.txn.is_creation` >>
   gvs[return_def, exactly_one_option_def, bind_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, return_def, raise_def, immutable_target_def,
       get_module_code_def, check_def, type_check_def, ignore_bind_def, assert_def,
       lift_sum_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   gvs[exactly_one_option_def, return_def, raise_def, bind_def,
       type_check_def, assert_def, get_module_code_def]) >>
  (* SOME case: immutables exist *)
  rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
  `IS_SOME (ALOOKUP r.immutables cx.txn.target)`
    by (drule assign_target_preserves_immutables_addr_dom >> simp[]) >>
  Cases_on `ALOOKUP r.immutables cx.txn.target` >> gvs[] >>
  `(IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)) ⇔
    IS_SOME (FLOOKUP (get_source_immutables (current_module cx) x') (string_to_num n)))`
    by (drule assign_target_preserves_immutables_dom >> simp[]) >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def, lift_sum_def, LET_THM,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
  CONV_TAC (RHS_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, bind_def, get_scopes_def,
       return_def, lift_sum_def, LET_THM, get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator])) >>
  Cases_on `cx.txn.is_creation` >>
  gvs[return_def, exactly_one_option_def, bind_def, get_address_immutables_def,
      lift_option_def, lift_option_type_def, return_def, raise_def, immutable_target_def,
      get_module_code_def, check_def, type_check_def, type_check_def, ignore_bind_def, assert_def,
      lift_sum_def] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)` >>
  gvs[] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) x') (string_to_num n)` >>
  gvs[] >>
  Cases_on `get_module_code cx (current_module cx)` >>
  gvs[return_def, raise_def] >>
  IF_CASES_TAC >> gvs[return_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def, bind_def,
      type_check_def, assert_def, get_module_code_def] >>
  rpt CASE_TAC
QED

Theorem name_lookup_after_update_target_replace:
  ∀cx st n av v.
    lookup_name_target cx st n = SOME av ⇒
    lookup_name (update_target cx st av (Replace v)) n = SOME v
Proof
  rw[lookup_name_target_def, lookup_base_target_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> Cases_on `q` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  `var_in_scope r n` by simp[var_in_scope_iff_lookup_name_typed, lookup_name_typed_def] >>
  simp[update_target_name_replace, lookup_after_update]
QED

Theorem name_lookup_after_update_target_update:
  ∀cx st n ty bop av v1 v2 v.
    lookup_name st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                   NoneTV bop v1 v2 = INL v ⇒
    lookup_name (update_target cx st av (Update ty bop v2)) n = SOME v
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def] >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  simp[update_target_def] >>
  `assign_target cx (BaseTargetV (ScopedVar n) []) (Update ty bop v2) st =
   (INL NONE, update_name st n v)` by (drule assign_target_name_update >> simp[]) >>
  simp[lookup_after_update]
QED

Theorem update_target_var_in_scope:
  ∀cx st av ao n.
    var_in_scope (update_target cx st av ao) n ⇔ var_in_scope st n
Proof
  rw[update_target_def, EQ_IMP_THM] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  `MAP FDOM r.scopes = MAP FDOM st.scopes`
    by (drule (CONJUNCT1 vyperScopePreservationTheory.assign_target_preserves_scopes_dom) >> simp[]) >>
  metis_tac[var_in_scope_dom_iff]
QED

Theorem lookup_name_target_is_valid_target_Replace:
  ∀cx st n av v.
    lookup_name_target cx st n = SOME av ⇒
    valid_target cx st av (Replace v)
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def] >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
  `var_in_scope st n` by simp[var_in_scope_iff_lookup_name_typed, lookup_name_typed_def] >>
  simp[valid_target_name_replace]
QED
