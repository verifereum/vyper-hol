Theory vyperUpdateTarget
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter vyperLookup vyperAssignTarget

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
  ∀cx st n bop v1 v2 v.
    evaluate_binop bop v1 v2 = INL v ∧
    lookup_name st n = SOME v1 ⇒
    update_target cx st (BaseTargetV (ScopedVar n) []) (Update bop v2) =
    update_name st n v
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_name_update >> simp[]
QED

Theorem valid_target_name_implies_var_in_scope:
  ∀cx st n ao. valid_target cx st (BaseTargetV (ScopedVar n) []) ao ⇒ var_in_scope st n
Proof
  rw[var_in_scope_def, lookup_name_def, valid_target_def] >>
  gvs[Once assign_target_def, bind_def, get_scopes_def, return_def,
      lift_option_def, lift_option_type_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[raise_def] >>
  irule find_containing_scope_lookup_scopes >> simp[]
QED

Theorem valid_target_name_replace:
  ∀cx st n v. var_in_scope st n ⇒ valid_target cx st (BaseTargetV (ScopedVar n) []) (Replace v)
Proof
  rw[var_in_scope_def, lookup_name_def, valid_target_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> gvs[] >>
  PairCases_on `x` >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, LET_THM, assign_subscripts_def, lift_sum_def,
       ignore_bind_def, set_scopes_def, assign_result_def]
QED

Theorem valid_target_name_update:
  ∀cx st n bop v1 v2 v.
    lookup_name st n = SOME v1 ∧
    evaluate_binop bop v1 v2 = INL v ⇒
    valid_target cx st (BaseTargetV (ScopedVar n) []) (Update bop v2)
Proof
  rw[lookup_name_def, valid_target_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `x2 = v1` by (drule find_containing_scope_lookup >> simp[]) >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, LET_THM, assign_subscripts_def, lift_sum_def,
       ignore_bind_def, set_scopes_def, assign_result_def]
QED

Theorem update_target_name_subscripts:
  ∀cx st n sbs ao a a'.
    lookup_name st n = SOME a ∧
    assign_subscripts a (REVERSE sbs) ao = INL a' ⇒
    update_target cx st (BaseTargetV (ScopedVar n) sbs) ao = update_name st n a'
Proof
  rw[update_target_def] >>
  imp_res_tac assign_target_name_subscripts_state >> simp[]
QED

Theorem valid_target_name_subscripts:
  ∀cx st n sbs ao a a'.
    lookup_name st n = SOME a ∧
    assign_subscripts a (REVERSE sbs) ao = INL a' ⇒
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
    valid_lookups cx st ∧ valid_target cx st av ao ⇒
    lookup_name_target cx (update_target cx st av ao) n = lookup_name_target cx st n
Proof
  rw[valid_lookups_def, valid_target_def, lookup_name_target_def,
     lookup_base_target_def, update_target_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  `MAP FDOM r.scopes = MAP FDOM st.scopes`
    by (drule (CONJUNCT1 vyperScopePreservationTheory.assign_target_preserves_scopes_dom) >> simp[]) >>
  `IS_SOME (lookup_scopes (string_to_num n) r.scopes) = IS_SOME (lookup_scopes (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_dom_iff] >>
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
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    lookup_name cx (update_target cx st av (Replace v)) n = SOME v
Proof
  rw[valid_lookups_def, lookup_name_target_def, lookup_base_target_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> Cases_on `q` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       lift_sum_def, LET_THM,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
  Cases_on `cx.txn.is_creation` >>
  gvs[return_def, bind_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
      immutable_target_def,
      option_CASE_rator, sum_CASE_rator, prod_CASE_rator,
      get_module_code_def, check_def, type_check_def, ignore_bind_def, assert_def, AllCaseEqs()] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  TRY (* ScopedVar cases *)
  (`var_in_scope r n` by simp[var_in_scope_def, lookup_name_def] >>
   simp[update_target_name_replace] >>
   `valid_lookups cx r` by (simp[valid_lookups_def] >> qexists_tac `imms` >> simp[]) >>
   `lookup_name (update_name r n v) n = SOME v` by simp[lookup_after_update] >>
   `valid_lookups cx (update_name r n v)`
     by metis_tac[valid_lookups_preserved_after_update_var_in_scope] >>
   drule lookup_name_implies_lookup_name >> simp[] >> NO_TAC) >>
  (* ImmutableVar case *)
  gvs[exactly_one_option_def] >>
  simp[update_target_def, Once assign_target_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def, LET_THM, return_def,
       assign_subscripts_def, lift_sum_def, ignore_bind_def, set_immutable_def,
       set_address_immutables_def, assign_result_def] >>
  simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def, lift_sum_def,
       get_source_immutables_def, set_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE, alistTheory.ALOOKUP_ADELKEY,
       exactly_one_option_def]
QED

Theorem name_lookup_after_update_target_update:
  ∀cx st n bop av v1 v2 v.
    valid_lookups cx st ∧
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ⇒
    lookup_name cx (update_target cx st av (Update bop v2)) n = SOME v
Proof
  rw[valid_lookups_def, lookup_name_target_def, lookup_base_target_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> Cases_on `q` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       lift_sum_def, LET_THM,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
  Cases_on `cx.txn.is_creation` >>
  gvs[return_def, bind_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
      immutable_target_def,
      option_CASE_rator, sum_CASE_rator, prod_CASE_rator,
      get_module_code_def, check_def, type_check_def, ignore_bind_def, assert_def, AllCaseEqs()] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  TRY (* ScopedVar cases *)
  (`var_in_scope r n` by simp[var_in_scope_def, lookup_name_def] >>
   `valid_lookups cx r` by (simp[valid_lookups_def] >> qexists_tac `imms` >> simp[]) >>
   `lookup_name r n = SOME v1` by (drule lookup_name_to_lookup_name >> simp[]) >>
   simp[update_target_def] >>
   `assign_target cx (BaseTargetV (ScopedVar n) []) (Update bop v2) r =
    (INL NONE, update_name r n v)` by (drule assign_target_name_update >> simp[]) >>
   simp[] >>
   `lookup_name (update_name r n v) n = SOME v` by simp[lookup_after_update] >>
   `valid_lookups cx (update_name r n v)`
     by metis_tac[valid_lookups_preserved_after_update_var_in_scope] >>
   drule lookup_name_implies_lookup_name >> simp[] >> NO_TAC) >>
  (* ImmutableVar case *)
  gvs[exactly_one_option_def] >>
  sg `lookup_immutable cx r n = SOME v1` >-
     (qpat_x_assum `lookup_name _ _ _ = _` mp_tac >>
      simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
           get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
           exactly_one_option_def, lift_sum_def, lookup_immutable_def]) >>
   simp[update_target_def, Once assign_target_def, bind_def, get_immutables_def,
        get_address_immutables_def, lift_option_def, lift_option_type_def, LET_THM, return_def,
        assign_subscripts_def, lift_sum_def, ignore_bind_def, set_immutable_def,
        set_address_immutables_def, lookup_immutable_def, assign_result_def] >>
   `x = v1` by gvs[lookup_immutable_def] >> gvs[return_def, raise_def] >>
   simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def, lift_sum_def,
        get_source_immutables_def, set_source_immutables_def,
        finite_mapTheory.FLOOKUP_UPDATE, alistTheory.ALOOKUP_ADELKEY,
        exactly_one_option_def]
QED

Theorem update_target_valid_lookups:
  ∀cx st av ao.
    valid_target cx st av ao ⇒
    (valid_lookups cx (update_target cx st av ao) ⇔ valid_lookups cx st)
Proof
  rw[valid_lookups_def, valid_target_def, update_target_def, EQ_IMP_THM] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  `MAP FDOM r.scopes = MAP FDOM st.scopes`
    by (drule (CONJUNCT1 vyperScopePreservationTheory.assign_target_preserves_scopes_dom) >> simp[]) >>
  (* Both directions use similar structure *)
  TRY (drule assign_target_preserves_immutables_addr_dom_rev >> simp[] >> strip_tac >>
       Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
       rpt strip_tac >>
       `var_in_scope r n` by (gvs[var_in_scope_def, lookup_name_def] >> metis_tac[lookup_scopes_dom_iff]) >>
       `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n) = NONE` by metis_tac[] >>
       drule assign_target_preserves_immutables_dom >> simp[] >> strip_tac >>
       first_x_assum (qspec_then `string_to_num n` mp_tac) >> gvs[] >> NO_TAC) >>
  drule assign_target_preserves_immutables_addr_dom >> simp[] >> strip_tac >>
  Cases_on `ALOOKUP r.immutables cx.txn.target` >> gvs[] >>
  rpt strip_tac >>
  `var_in_scope st n` by (gvs[var_in_scope_def, lookup_name_def] >> metis_tac[lookup_scopes_dom_iff]) >>
  `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n) = NONE` by metis_tac[] >>
  drule assign_target_preserves_immutables_dom >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `string_to_num n` mp_tac) >> gvs[]
QED

Theorem update_target_var_in_scope:
  ∀cx st av ao n.
    var_in_scope (update_target cx st av ao) n ⇔ var_in_scope st n
Proof
  rw[var_in_scope_def, lookup_name_def, update_target_def, EQ_IMP_THM] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  `MAP FDOM r.scopes = MAP FDOM st.scopes`
    by (drule (CONJUNCT1 vyperScopePreservationTheory.assign_target_preserves_scopes_dom) >> simp[]) >>
  metis_tac[lookup_scopes_dom_iff]
QED

Theorem lookup_name_target_is_valid_target_Replace:
  ∀cx st n av v.
    lookup_name_target cx st n = SOME av ⇒
    valid_target cx st av (Replace v)
Proof
  rw[lookup_name_target_def, lookup_base_target_def, valid_target_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> Cases_on `q` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       lift_sum_def, LET_THM,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator] >>
  Cases_on `cx.txn.is_creation` >>
  gvs[return_def, bind_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
      immutable_target_def, raise_def,
      option_CASE_rator, sum_CASE_rator, prod_CASE_rator,
      get_module_code_def, check_def, type_check_def, ignore_bind_def, assert_def, AllCaseEqs()] >-
  (* is_creation = T *)
  (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
   gvs[return_def, raise_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   Cases_on `FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num n)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   TRY
   (* ScopedVar case *)
   (`IS_SOME (find_containing_scope (string_to_num n) r.scopes)`
      by metis_tac[lookup_scopes_find_containing] >>
    Cases_on `find_containing_scope (string_to_num n) r.scopes` >> gvs[] >>
    PairCases_on `x'` >>
    simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
         lift_option_def, lift_option_type_def, LET_THM, assign_subscripts_def, lift_sum_def,
         ignore_bind_def, set_scopes_def, assign_result_def] >> NO_TAC) >>
   (* ImmutableVar case *)
   gvs[exactly_one_option_def] >>
   simp[Once assign_target_def, bind_def, get_immutables_def,
        get_address_immutables_def, lift_option_def, lift_option_type_def, LET_THM, return_def,
        assign_subscripts_def, lift_sum_def, ignore_bind_def,
        set_immutable_def, set_address_immutables_def, assign_result_def]) >>
  (* is_creation = F, must be ScopedVar *)
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `IS_SOME (find_containing_scope (string_to_num n) r.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) r.scopes` >> gvs[] >>
  PairCases_on `x` >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, LET_THM, assign_subscripts_def, lift_sum_def,
       ignore_bind_def, set_scopes_def, assign_result_def]
QED
