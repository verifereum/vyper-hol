Theory vyperAssignTargetSpec

Ancestors
  vyperInterpreter

Definition assign_target_spec_def:
  assign_target_spec cx st (av : assignment_value) (ao : assign_operation) Q ⇔
    case assign_target cx av ao st of
    | (INL _, st') => Q st'
    | (INR _, _) => F
End

Definition lookup_name_def:
  lookup_name cx st n =
    case eval_expr cx (Name n) st of
    | (INL (Value v), _) => SOME v
    | (_, _) => NONE
End

Definition lookup_base_target_def:
  lookup_base_target cx st tgt =
    case eval_base_target cx tgt st of
    | (INL (loc, sbs), _) => SOME (BaseTargetV loc sbs)
    | (INR _, _) => NONE
End

Definition lookup_name_target_def:
  lookup_name_target cx st n = lookup_base_target cx st (NameTarget n)
End

Definition is_valid_lookup_name_def:
  is_valid_lookup_name cx st n <=>
    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
    IS_SOME (lookup_name cx st n)
End

Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
End

Theorem assign_target_spec_consequence:
  ∀cx st av v Q Q'.
    (∀st'. Q st' ⇒ Q' st') ∧
    assign_target_spec cx st av (Replace v) Q ⇒
      assign_target_spec cx st av (Replace v) Q'
Proof
  rw[assign_target_spec_def] >> rpt strip_tac >>
  Cases_on `assign_target cx av (Replace v) st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

(**********************************************************************)
(* Helper lemmas *)

Theorem lookup_scopes_to_lookup_name:
  ∀cx st n v gbs.
    lookup_scopes (string_to_num n) st.scopes = SOME v ∧
    ALOOKUP st.globals cx.txn.target = SOME gbs ∧
    FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE ⇒
    lookup_name cx st n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, exactly_one_option_def, lift_sum_def]
QED

Theorem lookup_scopes_find_containing:
  ∀id sc. IS_SOME (lookup_scopes id sc) ⇒ IS_SOME (find_containing_scope id sc)
Proof
  Induct_on `sc` >- rw[lookup_scopes_def] >>
  rpt strip_tac >>
  simp[lookup_scopes_def, find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >-
   (simp[] >>
    first_x_assum (qspec_then `id` mp_tac) >>
    impl_tac >- fs[lookup_scopes_def] >>
    strip_tac >> Cases_on `find_containing_scope id sc` >> gvs[]) >>
  simp[]
QED

Theorem find_containing_scope_pre_none:
  ∀id sc pre env v rest.
    find_containing_scope id sc = SOME (pre,env,v,rest) ⇒
    lookup_scopes id pre = NONE
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  simp[find_containing_scope_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> gvs[] >-
   (strip_tac >> PairCases_on `z` >> gvs[] >> simp[lookup_scopes_def]) >>
  simp[lookup_scopes_def]
QED

Theorem lookup_scopes_update:
  ∀id pre env v rest.
    lookup_scopes id pre = NONE ⇒
    lookup_scopes id (pre ++ env |+ (id,v) :: rest) = SOME v
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[lookup_scopes_def, AllCaseEqs()]
QED

(**********************************************************************)

Theorem assign_target_spec_preserves_toplevel_name_targets:
  ∀P cx st av ao n.
    lookup_toplevel_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_toplevel_name_target cx st' n = SOME av')
Proof
  cheat
QED

Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  cheat
QED

(* TODO: this one lemma is not enough; we need to show that evaluation
doesn't change targets (evaluation may change values of variables, but
not what already existing variables are bound to) *)

Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    is_valid_lookup_name cx st n ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) (λst'. lookup_name cx st' n = SOME v)
Proof
  simp[is_valid_lookup_name_def, lookup_name_target_def, lookup_base_target_def, assign_target_spec_def, lookup_name_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `ALOOKUP st.globals cx.txn.target` >- fs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def] >-
  (simp[get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def,
        lift_sum_def, immutable_target_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >-
   (strip_tac >> gvs[] >>
    simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
    `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
      by metis_tac[lookup_scopes_find_containing] >>
    Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
    gvs[return_def, raise_def] >> PairCases_on `x'` >> gvs[] >>
    simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
         set_scopes_def, ignore_bind_def] >>
    `lookup_scopes (string_to_num n) x'0 = NONE`
      by metis_tac[find_containing_scope_pre_none] >>
    `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
      by metis_tac[lookup_scopes_update] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, lift_sum_def, exactly_one_option_def, return_def]) >>
   strip_tac >> gvs[] >>
   simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
        lift_option_def, get_immutables_def, get_immutables_module_def,
        get_current_globals_def, lift_sum_def, assign_subscripts_def,
        return_def, ignore_bind_def, set_immutable_def,
        lift_option_def, set_current_globals_def] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_immutables_module_def, get_current_globals_def,
        lift_option_def, get_module_globals_def, set_module_globals_def,
        finite_mapTheory.FLOOKUP_UPDATE, lift_sum_def,
        exactly_one_option_def, return_def]) >>
  simp[lift_sum_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x'` >> gvs[] >>
  simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
       set_scopes_def, ignore_bind_def] >>
  `lookup_scopes (string_to_num n) x'0 = NONE`
    by metis_tac[find_containing_scope_pre_none] >>
  `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
    by metis_tac[lookup_scopes_update] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, lift_sum_def, exactly_one_option_def, return_def] >>
  Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >-
  simp[exactly_one_option_def, return_def] >>
  fs[Once evaluate_def, bind_def, get_scopes_def, return_def,
     get_immutables_def, get_immutables_module_def, get_current_globals_def,
     lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >>
  gvs[exactly_one_option_def, raise_def]
QED
