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
  rw[assign_target_spec_def] >>
  drule assign_target_scoped_var_replace >>
  disch_then (qspecl_then [`cx`, `v`] strip_assume_tac) >>
  simp[]
QED

Theorem assign_target_spec_scoped_var_update_elim:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q ⇒
    Q (update_scoped_var st n v')
Proof
  rw[assign_target_spec_def] >>
  drule_all assign_target_scoped_var_update >>
  disch_then (qspec_then `cx` mp_tac) >> strip_tac >> gvs[]
QED

Theorem assign_target_spec_scoped_var_update_intro:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    Q (update_scoped_var st n v') ⇒
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q
Proof
  rw[assign_target_spec_def] >>
  drule_all assign_target_scoped_var_update >> simp[]
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
    IS_SOME (ALOOKUP st.immutables cx.txn.target) ∧
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  rename1 `assign_target cx av ao st = (INL res, st')` >>
  qpat_x_assum `_ = SOME av'` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >> simp[] >-
  ((* ScopedVar case *)
   Cases_on `cx.txn.is_creation` >>
   simp[return_def, get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >-
   (Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
    simp[lift_sum_def, exactly_one_option_def, return_def] >>
    Cases_on `exactly_one_option (SOME (ScopedVar n))
                (immutable_target (get_source_immutables NONE imms) n (string_to_num n))` >>
    simp[return_def, raise_def] >> strip_tac >> gvs[] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
    sg `IS_SOME (lookup_scopes (string_to_num n) st'.scopes)` >-
    (qpat_x_assum `assign_target _ _ _ _ = _`
       (mp_tac o MATCH_MP (CONJUNCT1 vyperScopePreservationLemmasTheory.assign_target_preserves_scopes_dom_lookup)) >>
     disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
    simp[] >>
    simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
    sg `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` >-
    (irule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_addr_dom >>
     qexistsl_tac [`ao`, `av`, `res`, `st`] >> simp[]) >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP st'.immutables cx.txn.target = SOME imms'` >>
    simp[lift_sum_def, exactly_one_option_def, return_def] >>
    Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
    gvs[exactly_one_option_def] >>
    Cases_on `immutable_target (get_source_immutables NONE imms') n (string_to_num n)` >>
    simp[exactly_one_option_def, return_def, raise_def] >>
    gvs[immutable_target_def] >>
    drule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_dom >>
    disch_then (qspecl_then [`string_to_num n`, `imms`, `imms'`] mp_tac) >> simp[] >>
    Cases_on `FLOOKUP (get_source_immutables NONE imms) (string_to_num n)` >>
    Cases_on `FLOOKUP (get_source_immutables NONE imms') (string_to_num n)` >> gvs[]) >>
   simp[lift_sum_def, exactly_one_option_def, return_def] >> strip_tac >> gvs[] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   sg `IS_SOME (lookup_scopes (string_to_num n) st'.scopes)` >-
   (qpat_x_assum `assign_target _ _ _ _ = _`
      (mp_tac o MATCH_MP (CONJUNCT1 vyperScopePreservationLemmasTheory.assign_target_preserves_scopes_dom_lookup)) >>
    disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
   simp[lift_sum_def, exactly_one_option_def, return_def]) >>
  (* Not in scopes - ImmutableVar case *)
  Cases_on `cx.txn.is_creation` >> simp[return_def] >-
  (simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
   rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
   simp[lift_sum_def, exactly_one_option_def] >>
   Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
   simp[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   `lookup_scopes (string_to_num n) st'.scopes = NONE` by
     (qpat_x_assum `assign_target _ _ _ _ = _`
        (mp_tac o MATCH_MP (CONJUNCT1 vyperScopePreservationLemmasTheory.assign_target_preserves_scopes_dom_lookup)) >>
      disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
   simp[] >>
   simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
   sg `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` >-
   (irule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_addr_dom >>
    qexistsl_tac [`ao`, `av`, `res`, `st`] >> simp[]) >>
   Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
   rename1 `ALOOKUP st'.immutables cx.txn.target = SOME imms'` >>
   simp[lift_sum_def, exactly_one_option_def] >>
   rename1 `immutable_target _ n _ = SOME tgt` >>
   sg `immutable_target (get_source_immutables NONE imms') n (string_to_num n) = SOME tgt` >-
   (gvs[immutable_target_def] >>
    drule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_dom >>
    disch_then (qspecl_then [`string_to_num n`, `imms`, `imms'`] mp_tac) >> simp[] >>
    Cases_on `FLOOKUP (get_source_immutables NONE imms) (string_to_num n)` >>
    Cases_on `FLOOKUP (get_source_immutables NONE imms') (string_to_num n)` >> gvs[]) >>
   simp[exactly_one_option_def, return_def]) >>
  simp[lift_sum_def, exactly_one_option_def, raise_def]
QED

(* Theorem showing that after assign_target, lookup_name returns the new value.
   Handles both ScopedVar and ImmutableVar cases. *)
Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av (Replace v) st` >> Cases_on `q` >> gvs[] >>
  rename1 `assign_target cx av (Replace v) st = (INL res, st')` >>
  (* Case split on what av is - it comes from lookup_name_target *)
  qpat_x_assum `lookup_name_target cx st n = SOME av` mp_tac >>
  simp[lookup_name_target_def, lookup_base_target_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >> simp[] >-
  ((* ScopedVar case: n is in scopes *)
   Cases_on `cx.txn.is_creation` >> simp[return_def] >-
   ((* is_creation case *)
    simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
    fs[valid_lookups_def] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
    simp[lift_sum_def, exactly_one_option_def] >>
    Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
    simp[exactly_one_option_def, return_def, raise_def] >>
    strip_tac >> gvs[] >>
    (* av = BaseTargetV (ScopedVar n) [] *)
    `var_in_scope st n` by fs[var_in_scope_def, lookup_scoped_var_def] >>
    drule assign_target_scoped_var_replace >>
    disch_then (qspecl_then [`cx`, `v`] strip_assume_tac) >> gvs[] >>
    `lookup_scoped_var (update_scoped_var st n v) n = SOME v` by simp[lookup_after_update] >>
   sg `valid_lookups cx (update_scoped_var st n v)` >-
   (fs[valid_lookups_def] >> qexists_tac `imms` >>
    simp[immutables_preserved_after_update] >> rpt strip_tac >>
    rename1 `var_in_scope _ varname` >>
    (* Show var_in_scope st varname *)
    Cases_on `n = varname` >-
    (* n = varname: use existing var_in_scope st n, plus immutable_target *)
    (gvs[immutable_target_def, AllCaseEqs()]) >>
    (* n ≠ varname: derive from lookup_scoped_var_preserved_after_update *)
    `var_in_scope st varname` by gvs[var_in_scope_def, lookup_scoped_var_def, lookup_scoped_var_preserved_after_update] >>
    first_x_assum drule >> simp[]) >>
   irule lookup_scoped_var_implies_lookup_name >> simp[]) >>
   (* non-creation case *)
   simp[lift_sum_def, exactly_one_option_def] >> strip_tac >> gvs[] >>
   `var_in_scope st n` by fs[var_in_scope_def, lookup_scoped_var_def] >>
   drule assign_target_scoped_var_replace >>
   disch_then (qspecl_then [`cx`, `v`] strip_assume_tac) >> gvs[] >>
   `lookup_scoped_var (update_scoped_var st n v) n = SOME v` by simp[lookup_after_update] >>
   sg `valid_lookups cx (update_scoped_var st n v)` >-
   (fs[valid_lookups_def] >> qexists_tac `imms` >>
    simp[immutables_preserved_after_update] >> rpt strip_tac >>
    rename1 `var_in_scope _ varname` >>
    (* Show var_in_scope st varname, then apply the forall *)
    `var_in_scope st varname` by
      (Cases_on `n = varname` >> gvs[var_in_scope_def, lookup_scoped_var_def, lookup_scoped_var_preserved_after_update]) >>
    first_x_assum drule >> simp[]) >>
   (* Show st' = update_scoped_var st n v, then use lookup_after_update *)
   qpat_x_assum `_ = SOME av` mp_tac >> simp[return_def] >> strip_tac >> gvs[] >>
   irule lookup_scoped_var_implies_lookup_name >> simp[]) >>
  (* ImmutableVar case: n is NOT in scopes, must be in immutables *)
  Cases_on `cx.txn.is_creation` >> simp[return_def] >-
  ((* is_creation: immutable assignment *)
   simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
   fs[valid_lookups_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
   rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
   simp[lift_sum_def, exactly_one_option_def] >>
   Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
   simp[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   gvs[immutable_target_def, AllCaseEqs()] >>
   `lookup_immutable cx st' n = SOME v` by
     (irule assign_target_immutable_replace_gives_lookup >>
      qexistsl_tac [`res`, `st`] >> simp[lookup_immutable_def]) >>
   sg `valid_lookups cx st'` >-
   (rw[valid_lookups_def] >>
    sg `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` >-
    (irule assign_target_preserves_immutables_addr_dom >>
     qexistsl_tac [`Replace v`, `BaseTargetV (ImmutableVar n) []`, `res`, `st`] >> simp[]) >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[] >>
    rpt strip_tac >> rename1 `var_in_scope st' varname` >>
    `var_in_scope st varname` by
      (fs[var_in_scope_def, lookup_scoped_var_def] >>
       qpat_x_assum `assign_target _ _ _ _ = _`
         (mp_tac o MATCH_MP (CONJUNCT1 assign_target_preserves_scopes_dom_lookup)) >>
       simp[]) >>
    `FLOOKUP (get_source_immutables NONE imms) (string_to_num varname) = NONE` by simp[] >>
    drule assign_target_preserves_immutables_dom >>
    disch_then (qspecl_then [`string_to_num varname`, `imms`, `x`] mp_tac) >> simp[]) >>
   irule lookup_immutable_implies_lookup_name >> simp[]) >>
  (* non-creation: no immutable lookup, so lookup_name_target should have failed *)
  simp[lift_sum_def, exactly_one_option_def, raise_def]
QED

(* Similar to assign_target_spec_lookup but for aug-assignment.
   Handles both ScopedVar and ImmutableVar cases. *)
Theorem assign_target_spec_update:
  ∀cx st n bop av v1 v2 v.
    valid_lookups cx st ∧
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target_spec cx st av (Update bop v2) P ⇒
    assign_target_spec cx st av (Update bop v2) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av (Update bop v2) st` >> Cases_on `q` >> gvs[] >>
  rename1 `assign_target cx av (Update bop v2) st = (INL res, st')` >>
  (* Case split on what av is - it comes from lookup_name_target *)
  qpat_x_assum `lookup_name_target cx st n = SOME av` mp_tac >>
  simp[lookup_name_target_def, lookup_base_target_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >> simp[] >-
  ((* ScopedVar case: n is in scopes *)
   Cases_on `cx.txn.is_creation` >> simp[return_def] >-
   ((* is_creation case *)
    simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
    fs[valid_lookups_def] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
    simp[lift_sum_def, exactly_one_option_def] >>
    Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
    simp[exactly_one_option_def, return_def, raise_def] >-
    ((* immutable_target = NONE case *)
     strip_tac >> gvs[] >>
     (* av = BaseTargetV (ScopedVar n) [] *)
     (* Get lookup_scoped_var st n = SOME v1 from lookup_name *)
    `lookup_scoped_var st n = SOME v1` by
       (fs[lookup_name_def, lookup_scoped_var_def] >>
        qpat_x_assum `(case _ of _ => _) = SOME v1` mp_tac >>
        simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
             get_immutables_def, get_address_immutables_def, lift_option_def] >>
        simp[immutable_target_def, exactly_one_option_def, lift_sum_def, return_def] >>
        gvs[AllCaseEqs()] >>
        Cases_on `lookup_scopes (string_to_num n) st.scopes` >>
        gvs[exactly_one_option_def, return_def] >>
        fs[immutable_target_def] >> gvs[AllCaseEqs()] >>
        simp[exactly_one_option_def, return_def]) >>
    drule_all assign_target_scoped_var_update >>
    disch_then (qspec_then `cx` mp_tac) >> strip_tac >> gvs[] >>
    `lookup_scoped_var (update_scoped_var st n v) n = SOME v` by simp[lookup_after_update] >>
    sg `valid_lookups cx (update_scoped_var st n v)` >-
    (fs[valid_lookups_def] >> qexists_tac `imms` >>
     simp[immutables_preserved_after_update] >> rpt strip_tac >>
     rename1 `var_in_scope _ varname` >>
     Cases_on `n = varname` >- gvs[immutable_target_def, AllCaseEqs()] >>
     `var_in_scope st varname` by gvs[var_in_scope_def, lookup_scoped_var_def, lookup_scoped_var_preserved_after_update] >>
     first_x_assum drule >> simp[]) >>
    irule lookup_scoped_var_implies_lookup_name >> simp[]) >>
    (* immutable_target = SOME x case: contradiction with valid_lookups *)
    (* n is in scopes, so by valid_lookups it can't be in immutables *)
    `var_in_scope st n` by fs[var_in_scope_def, lookup_scoped_var_def] >>
    first_x_assum drule >> strip_tac >>
    gvs[immutable_target_def, AllCaseEqs()]) >>
   (* non-creation case *)
   simp[lift_sum_def, exactly_one_option_def, return_def] >> strip_tac >> gvs[] >>
   fs[valid_lookups_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
   rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
   `lookup_scoped_var st n = SOME v1` by
      (fs[lookup_name_def, lookup_scoped_var_def] >>
       qpat_x_assum `(case _ of _ => _) = SOME v1` mp_tac >>
       simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
            get_immutables_def, get_address_immutables_def, lift_option_def] >>
       gvs[AllCaseEqs()] >>
       Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[] >>
       Cases_on `FLOOKUP (get_source_immutables NONE imms) (string_to_num n)` >>
       simp[exactly_one_option_def, lift_sum_def, return_def, raise_def]) >>
   drule_all assign_target_scoped_var_update >>
   disch_then (qspec_then `cx` mp_tac) >> strip_tac >> gvs[] >>
   `lookup_scoped_var (update_scoped_var st n v) n = SOME v` by simp[lookup_after_update] >>
   sg `valid_lookups cx (update_scoped_var st n v)` >-
   (simp[valid_lookups_def] >> qexists_tac `imms` >>
    simp[immutables_preserved_after_update] >> rpt strip_tac >>
    rename1 `var_in_scope _ varname` >>
    `var_in_scope st varname` by
      (Cases_on `n = varname` >> gvs[var_in_scope_def, lookup_scoped_var_def, lookup_scoped_var_preserved_after_update]) >>
    first_x_assum drule >> simp[]) >>
   irule lookup_scoped_var_implies_lookup_name >> simp[]) >>
  (* ImmutableVar case: n is NOT in scopes, must be in immutables *)
  Cases_on `cx.txn.is_creation` >> simp[return_def] >-
  ((* is_creation: immutable aug-assignment *)
   simp[get_immutables_def, get_address_immutables_def, bind_def, lift_option_def] >>
   fs[valid_lookups_def] >>
   simp[return_def, lift_sum_def, exactly_one_option_def] >>
   Cases_on `immutable_target (get_source_immutables NONE imms) n (string_to_num n)` >>
   simp[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[immutable_target_def, AllCaseEqs()] >>
   sg `lookup_immutable cx st n = SOME v1` >-
   (simp[lookup_immutable_def] >>
    qpat_x_assum `lookup_name cx st n = SOME v1` mp_tac >>
    simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_address_immutables_def, lift_option_def] >>
    simp[lift_sum_def, exactly_one_option_def, return_def]) >>
   `lookup_immutable cx st' n = SOME v` by
     (irule assign_target_immutable_update_gives_lookup >>
      qexistsl_tac [`bop`, `res`, `st`, `v1`, `v2`] >> simp[]) >>
   sg `valid_lookups cx st'` >-
   (rw[valid_lookups_def] >>
    sg `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` >-
    (irule assign_target_preserves_immutables_addr_dom >>
     qexistsl_tac [`Update bop v2`, `BaseTargetV (ImmutableVar n) []`, `res`, `st`] >> simp[]) >>
    Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[] >>
    rpt strip_tac >> rename1 `var_in_scope st' varname` >>
    `var_in_scope st varname` by
      (fs[var_in_scope_def, lookup_scoped_var_def] >>
       qpat_x_assum `assign_target _ _ _ _ = _`
         (mp_tac o MATCH_MP (CONJUNCT1 assign_target_preserves_scopes_dom_lookup)) >>
       simp[]) >>
    `FLOOKUP (get_source_immutables NONE imms) (string_to_num varname) = NONE` by simp[] >>
    drule assign_target_preserves_immutables_dom >>
    disch_then (qspecl_then [`string_to_num varname`, `imms`, `x`] mp_tac) >> simp[]) >>
   irule lookup_immutable_implies_lookup_name >> simp[]) >>
  (* non-creation: no immutable lookup, so lookup_name_target should have failed *)
  simp[lift_sum_def, exactly_one_option_def, raise_def]
QED

Theorem assign_target_spec_preserves_valid_lookups:
  ∀cx st n v.
    valid_lookups cx st ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ valid_lookups cx st')
Proof
  rw[valid_lookups_def, assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  rename1 `assign_target cx av ao st = (INL res, st')` >>
  (* Show immutables address is preserved *)
  sg `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` >-
  (irule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_addr_dom >>
   qexistsl_tac [`ao`, `av`, `res`, `st`] >> simp[]) >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >> gvs[] >>
  rename1 `ALOOKUP st'.immutables cx.txn.target = SOME imms'` >>
  rpt strip_tac >>
  rename1 `var_in_scope st' varname` >>
  (* var_in_scope st' varname → var_in_scope st varname (by scopes domain preservation) *)
  `var_in_scope st varname` by
    (fs[var_in_scope_def, lookup_scoped_var_def] >>
     qpat_x_assum `assign_target _ _ _ _ = _`
       (mp_tac o MATCH_MP (CONJUNCT1 vyperScopePreservationLemmasTheory.assign_target_preserves_scopes_dom_lookup)) >>
     simp[]) >>
  (* Therefore FLOOKUP imms (string_to_num varname) = NONE *)
  first_x_assum drule >> strip_tac >>
  (* Show FLOOKUP imms' (string_to_num varname) = NONE by domain preservation *)
  drule vyperAssignTargetLemmasTheory.assign_target_preserves_immutables_dom >>
  disch_then (qspecl_then [`string_to_num varname`, `imms`, `imms'`] mp_tac) >> simp[]
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
