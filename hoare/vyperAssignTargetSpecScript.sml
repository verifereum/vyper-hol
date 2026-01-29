Theory vyperAssignTargetSpec

Ancestors
  vyperInterpreter vyperTypeValue vyperLookup vyperAssignTargetLemmas
  vyperScopePreservationLemmas

Definition assign_target_spec_def:
  assign_target_spec cx st (av : assignment_value) (ao : assign_operation) Q ⇔
    case assign_target cx av ao st of
    | (INL _, st') => Q st'
    | (INR _, _) => F
End

Theorem assign_target_spec_consequence:
  ∀cx st av ao Q Q'.
    (∀st'. Q st' ⇒ Q' st') ∧
    assign_target_spec cx st av ao Q ⇒
      assign_target_spec cx st av ao Q'
Proof
  rw[assign_target_spec_def] >> rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_scoped_var_replace_elim:
  ∀cx st n v Q. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q ⇒
                Q (update_scoped_var st n v)
Proof
  rw[assign_target_spec_def, update_scoped_var_def, Once assign_target_def,
     bind_def, get_scopes_def, return_def, lift_option_def, lift_sum_def,
     set_scopes_def, assign_subscripts_def, ignore_bind_def] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def, set_scopes_def, ignore_bind_def] >>
  PairCases_on `x` >> gvs[return_def, set_scopes_def, bind_def, ignore_bind_def]
QED

Theorem assign_target_spec_scoped_var_replace_intro:
  ∀cx st n v Q.
    var_in_scope st n ∧
    Q (update_scoped_var st n v) ⇒
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q
Proof
  rpt strip_tac >>
  fs[var_in_scope_def, lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[assign_target_spec_def, Once assign_target_def, bind_def,
       get_scopes_def, return_def, lift_option_def, lift_sum_def,
       assign_subscripts_def, ignore_bind_def, set_scopes_def] >>
  fs[update_scoped_var_def, LET_THM]
QED

Theorem assign_target_spec_scoped_var_update_elim:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q ⇒
    Q (update_scoped_var st n v')
Proof
  rw[assign_target_spec_def, update_scoped_var_def, Once assign_target_def,
     bind_def, get_scopes_def, return_def, lift_option_def, lift_sum_def,
     set_scopes_def, assign_subscripts_def, ignore_bind_def,
     lookup_scoped_var_def] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def, set_scopes_def, ignore_bind_def, bind_def] >>
  PairCases_on `x` >> gvs[return_def, set_scopes_def, bind_def, ignore_bind_def] >>
  drule_all find_containing_scope_lookup >> strip_tac >> gvs[return_def, raise_def]
QED

Theorem assign_target_spec_scoped_var_update_intro:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    Q (update_scoped_var st n v') ⇒
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q
Proof
  rpt strip_tac >>
  fs[lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[assign_target_spec_def, Once assign_target_def, bind_def,
       get_scopes_def, return_def, lift_option_def, lift_sum_def,
       assign_subscripts_def, ignore_bind_def, set_scopes_def] >>
  `x2 = v0` by (drule_all find_containing_scope_lookup >> gvs[]) >>
  gvs[return_def, raise_def] >>
  fs[update_scoped_var_def, LET_THM]
QED

Theorem assign_target_spec_pure:
  ∀cx st av ao P Q.
    P ∧ assign_target_spec cx st av ao Q ⇒
    assign_target_spec cx st av ao (λst'. P ∧ Q st')
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_conj:
  ∀cx st av ao Q1 Q2.
    assign_target_spec cx st av ao Q1 ∧
    assign_target_spec cx st av ao Q2 ⇒
    assign_target_spec cx st av ao (λst'. Q1 st' ∧ Q2 st')
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_preserves_toplevel_name_targets:
  ∀P cx st av ao n.
    lookup_toplevel_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_toplevel_name_target cx st' n = SOME av')
Proof
  simp[assign_target_spec_def, lookup_toplevel_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  Cases_on `n` >>
  simp[Once evaluate_def, return_def] >>
  fs[Once evaluate_def, return_def]
QED

Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `(_ = SOME av')` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[] >-
  ((* is_creation case *)
   simp[get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def, lift_sum_def,
        immutable_target_def] >>
   Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   Cases_on `FLOOKUP (get_module_globals NONE x').immutables (string_to_num n)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >-
   ((* ScopedVar case *)
    strip_tac >> gvs[] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def,
         get_current_globals_def, lift_option_def, lift_sum_def,
         immutable_target_def] >>
    `IS_SOME (lookup_scopes (string_to_num n) r.scopes)`
      by metis_tac[assign_target_preserves_scopes_dom_lookup] >>
    `IS_SOME (ALOOKUP r.globals cx.txn.target)`
      by (drule assign_target_preserves_globals_dom >> simp[]) >>
    Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    `FLOOKUP (get_module_globals NONE x'').immutables (string_to_num n) = NONE`
      by (drule assign_target_preserves_immutables_dom >>
          disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
    gvs[exactly_one_option_def, return_def]) >-
   ((* ImmutableVar case *)
    strip_tac >> gvs[] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def,
         get_current_globals_def, lift_option_def, lift_sum_def,
         immutable_target_def] >>
    `lookup_scopes (string_to_num n) r.scopes = NONE`
      by metis_tac[assign_target_preserves_scopes_dom_lookup,
                   optionTheory.IS_SOME_DEF, optionTheory.option_CLAUSES] >>
    `IS_SOME (ALOOKUP r.globals cx.txn.target)`
      by (drule assign_target_preserves_globals_dom >> simp[]) >>
    Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP r.globals cx.txn.target = SOME gbs'` >>
    `IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables (string_to_num n))`
      by (drule assign_target_preserves_immutables_dom >>
          disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
    Cases_on `FLOOKUP (get_module_globals NONE gbs').immutables (string_to_num n)` >>
    gvs[exactly_one_option_def, return_def])) >-
  ((* non-creation case *)
   simp[return_def, lift_sum_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   `IS_SOME (lookup_scopes (string_to_num n) r.scopes)`
     by metis_tac[assign_target_preserves_scopes_dom_lookup] >>
   gvs[lift_sum_def, exactly_one_option_def, return_def])
QED

Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  simp[valid_lookups_def, lookup_name_target_def, lookup_base_target_def,
       assign_target_spec_def, lookup_name_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `assign_target cx (BaseTargetV loc sbs) (Replace v) st` >>
  Cases_on `q` >-
  (* assign_target succeeded *)
  (gvs[] >>
   qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   Cases_on `cx.txn.is_creation` >-
   (* is_creation = T *)
   (gvs[return_def, get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def, lift_sum_def,
        immutable_target_def] >>
    Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
    Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)` >>
    fs[exactly_one_option_def, return_def, raise_def] >-
    (* ScopedVar case: IS_SOME scopes, FLOOKUP = NONE *)
    (strip_tac >> gvs[] >>
     qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
     simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
     `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
       by metis_tac[lookup_scopes_find_containing] >>
     Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
     gvs[return_def, raise_def] >> PairCases_on `x'` >>
     simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
          set_scopes_def, ignore_bind_def] >>
     strip_tac >> gvs[] >>
     `lookup_scopes (string_to_num n) x'0 = NONE`
       by metis_tac[find_containing_scope_pre_none] >>
     `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
       by metis_tac[lookup_scopes_update] >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          get_immutables_def, get_immutables_module_def, get_current_globals_def,
          lift_option_def, lift_sum_def, exactly_one_option_def, return_def]) >-
    (* ImmutableVar case: NOT IS_SOME scopes, FLOOKUP = SOME *)
    (strip_tac >> gvs[] >>
     qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
     simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
          lift_option_def, get_immutables_def, get_immutables_module_def,
          get_current_globals_def, lift_sum_def, assign_subscripts_def,
          return_def, ignore_bind_def, set_immutable_def,
          lift_option_def, set_current_globals_def] >>
     strip_tac >> gvs[] >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          get_immutables_def, get_immutables_module_def, get_current_globals_def,
          lift_option_def, get_module_globals_def, set_module_globals_def,
          finite_mapTheory.FLOOKUP_UPDATE, lift_sum_def,
          exactly_one_option_def, return_def])) >>
   (* is_creation = F *)
   gvs[return_def, lift_sum_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
   simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
   `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
     by metis_tac[lookup_scopes_find_containing] >>
   Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
   gvs[return_def, raise_def] >> PairCases_on `x'` >>
   simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
        set_scopes_def, ignore_bind_def] >>
   strip_tac >> gvs[] >>
   `lookup_scopes (string_to_num n) x'0 = NONE`
     by metis_tac[find_containing_scope_pre_none] >>
   `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
     by metis_tac[lookup_scopes_update] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   simp[get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def, lift_sum_def] >>
   Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)` >>
   simp[exactly_one_option_def, return_def] >>
   (* Contradiction: both scopes and immutables have the var *)
   fs[var_in_scope_def, lookup_scoped_var_def] >>
   first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  (* assign_target failed *)
  simp[] >> fs[]
QED

Theorem assign_target_spec_update:
  ∀cx st n bop av v1 v2 v.
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target_spec cx st av (Update bop v2) P ⇒
    assign_target_spec cx st av (Update bop v2) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def,
       lookup_name_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av (Update bop v2) st` >> Cases_on `q` >> gvs[] >>
  (* Analyze eval_base_target *)
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >-
  (* is_creation = T *)
  (gvs[return_def, get_immutables_def, get_immutables_module_def, bind_def,
       get_current_globals_def, lift_option_def, return_def, lift_sum_def,
       immutable_target_def] >>
   Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   Cases_on `FLOOKUP (get_module_globals NONE x').immutables (string_to_num n)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >-
   (* ScopedVar case *)
   (strip_tac >> gvs[] >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
    `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
      by metis_tac[lookup_scopes_find_containing] >>
    Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
    gvs[return_def, raise_def] >> PairCases_on `x''` >>
    simp[bind_def, lift_sum_def, assign_subscripts_def, set_scopes_def,
         ignore_bind_def, return_def] >>
    `lookup_scopes (string_to_num n) st.scopes = SOME x''2`
      by metis_tac[find_containing_scope_lookup] >>
    (* Show x''2 = v1 *)
    `x''2 = v1` by (
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
           get_immutables_def, get_immutables_module_def, get_current_globals_def,
           lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
    gvs[return_def, raise_def] >>
    strip_tac >> gvs[] >>
    `lookup_scopes (string_to_num n) x''0 = NONE`
      by metis_tac[find_containing_scope_pre_none] >>
    `lookup_scopes (string_to_num n) (x''0 ++ x''1 |+ (string_to_num n,v)::x''3) = SOME v`
      by metis_tac[lookup_scopes_update] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, lift_sum_def, exactly_one_option_def, return_def]) >>
   (* ImmutableVar case *)
   strip_tac >> gvs[] >>
   qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
   simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
        lift_option_def, get_immutables_def, get_immutables_module_def,
        get_current_globals_def, lift_sum_def, assign_subscripts_def,
        return_def, ignore_bind_def, set_immutable_def, set_current_globals_def] >>
   (* Show x'' = v1 *)
   `x'' = v1` by (
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          get_immutables_def, get_immutables_module_def, get_current_globals_def,
          lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
   gvs[return_def, raise_def] >>
   strip_tac >> gvs[] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_immutables_module_def, get_current_globals_def,
        lift_option_def, get_module_globals_def, set_module_globals_def,
        finite_mapTheory.FLOOKUP_UPDATE, lift_sum_def,
        exactly_one_option_def, return_def]) >>
  (* is_creation = F *)
  gvs[return_def, lift_sum_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x'` >>
  simp[bind_def, lift_sum_def, assign_subscripts_def, set_scopes_def,
       ignore_bind_def, return_def] >>
  `lookup_scopes (string_to_num n) st.scopes = SOME x'2`
    by metis_tac[find_containing_scope_lookup] >>
  (* Show x'2 = v1 *)
  `x'2 = v1` by (
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def] >>
    Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
    gvs[exactly_one_option_def, return_def, raise_def]) >>
  gvs[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `lookup_scopes (string_to_num n) x'0 = NONE`
    by metis_tac[find_containing_scope_pre_none] >>
  `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
    by metis_tac[lookup_scopes_update] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, lift_sum_def, exactly_one_option_def, return_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >-
  (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_immutables_module_def, get_current_globals_def,
        lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
  Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >-
  simp[exactly_one_option_def, return_def] >>
  (* Contradiction: both scopes and immutables have the var *)
  fs[Once evaluate_def, bind_def, get_scopes_def, return_def,
     get_immutables_def, get_immutables_module_def, get_current_globals_def,
     lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]
QED

Theorem assign_target_spec_preserves_valid_lookups:
  ∀cx st n v.
    valid_lookups cx st ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ valid_lookups cx st')
Proof
  rw[assign_target_spec_def, valid_lookups_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >>
  Cases_on `q` >> gvs[] >>
  `IS_SOME (ALOOKUP r.globals cx.txn.target)`
    by (drule assign_target_preserves_globals_dom >> simp[]) >>
  Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[] >>
  rpt strip_tac >>
  `var_in_scope st n`
    by (fs[var_in_scope_def, lookup_scoped_var_def] >>
        metis_tac[CONJUNCT1 assign_target_preserves_scopes_dom_lookup]) >>
  `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE`
    by metis_tac[] >>
  drule assign_target_preserves_immutables_dom >>
  disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]
QED

Theorem assign_target_spec_preserves_var_in_scope:
  ∀cx st n v.
    var_in_scope st n ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ var_in_scope st' n)
Proof
  rpt strip_tac >>
  simp[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >-
  (conj_tac >- fs[assign_target_spec_def] >>
   fs[var_in_scope_def, lookup_scoped_var_def] >>
   metis_tac[CONJUNCT1 assign_target_preserves_scopes_dom_lookup]) >>
  fs[assign_target_spec_def]
QED
