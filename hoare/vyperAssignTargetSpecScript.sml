Theory vyperAssignTargetSpec

Ancestors
  vyperInterpreter vyperTypeValue vyperLookup

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
  ∀cx st n Q. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q ⇒
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

(**********************************************************************)
(* Helper lemmas *)

Theorem ALOOKUP_set_module_globals_preserves:
  ∀al k v tgt. IS_SOME (ALOOKUP al tgt) ⇒ IS_SOME (ALOOKUP ((k, v) :: ADELKEY k al) tgt)
Proof
  rpt strip_tac >> Cases_on `k = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]
QED

Theorem assign_target_preserves_scopes:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes)))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
       ignore_bind_def, set_scopes_def] >-
  ((* ScopedVar case *)
   simp[AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
   strip_tac >> gvs[] >>
   rpt (qpat_x_assum `(case _ of NONE => _ | SOME v => _) _ = _` mp_tac) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `(case find_containing_scope _ _ of _ => _ | _ => _) _ = _` mp_tac >>
   simp[AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[] >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
   PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   `s''.scopes = x0 ++ [x1] ++ x3 ∧ FLOOKUP x1 (string_to_num id) = SOME x2`
     by (drule find_containing_scope_structure >> simp[]) >>
   metis_tac[lookup_scopes_update_preserves]) >-
  ((* TopLevelVar case *)
   strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, lookup_global_def,
                    bind_def, get_current_globals_def, lift_option_def, LET_THM,
                    set_global_def, set_current_globals_def] >>
   rpt (qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `(case ALOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac >>
   simp[AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[] >>
   rpt (FIRST [qpat_x_assum `(case ALOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case assign_toplevel _ _ _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case get_module_code _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case FLOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac]) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   gvs[AllCaseEqs(), return_def, raise_def] >>
   `st.scopes = s'⁵'.scopes` by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s'⁵'.scopes = s''.scopes` by (Cases_on `FLOOKUP (get_module_globals src_id_opt gbs).mutables (string_to_num id)` >> gvs[return_def, raise_def]) >>
   `s''.scopes = s'³'.scopes` by (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
   `s'³'.scopes = s'⁴'.scopes` by (Cases_on `assign_toplevel (type_env ts) res (REVERSE is) ao` >> gvs[return_def, raise_def]) >>
   `s'⁴'.scopes = s'⁶'.scopes` by (Cases_on `ALOOKUP s'⁴'.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   gvs[]) >-
  ((* ImmutableVar case *)
   strip_tac >> gvs[get_immutables_def, get_immutables_module_def, bind_def,
                    get_current_globals_def, lift_option_def, AllCaseEqs(), return_def,
                    raise_def, LET_THM, set_immutable_def, set_current_globals_def] >>
   `st.scopes = s''.scopes` by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s''.scopes = s'³'.scopes` by (Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num id)` >> gvs[return_def, raise_def]) >>
   `s'³'.scopes = s'⁴'.scopes` by (Cases_on `assign_subscripts a (REVERSE is) ao` >> gvs[return_def, raise_def]) >>
   `s'⁴'.scopes = s'⁶'.scopes` by (Cases_on `ALOOKUP s'⁴'.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   gvs[]) >-
  ((* TupleTargetV case *)
   rpt strip_tac >> gvs[check_def, AllCaseEqs(), return_def, raise_def] >>
   first_x_assum drule >> simp[] >>
   strip_tac >> gvs[assert_def, AllCaseEqs(), return_def, raise_def]) >-
  ((* assign_targets cons case *)
   rpt strip_tac >> gvs[get_Value_def, AllCaseEqs(), return_def, raise_def] >>
   Cases_on `tw` >> gvs[get_Value_def, return_def, raise_def] >>
   first_x_assum (qspec_then `s''` mp_tac) >> simp[] >>
   first_x_assum drule >> simp[])
QED

(* Helper lemma for TupleTargetV + TupleV case of the induction *)
Theorem assign_target_tuple_preserves_globals_and_immutables:
  ∀cx gvs vs.
    (∀st res st'.
       assign_targets cx gvs vs st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
       ∀n gbs gbs'.
         ALOOKUP st.globals cx.txn.target = SOME gbs ∧
         ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
         (IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) ⇔
          IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))) ⇒
    ∀st res st'.
      assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) st = (INL res,st') ⇒
      (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
      ∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        (IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) ⇔
         IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once assign_target_def, check_def, AllCaseEqs(), return_def, raise_def] >>
  simp[bind_def, ignore_bind_def, assert_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Helper lemma for assign_targets cons case of the induction *)
Theorem assign_targets_cons_preserves_globals_and_immutables:
  ∀cx av v gvs vs.
    (∀st res st'.
       assign_target cx av (Replace v) st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
       ∀n gbs gbs'.
         ALOOKUP st.globals cx.txn.target = SOME gbs ∧
         ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
         (IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) ⇔
          IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))) ∧
    (∀st res st'.
       assign_targets cx gvs vs st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
       ∀n gbs gbs'.
         ALOOKUP st.globals cx.txn.target = SOME gbs ∧
         ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
         (IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) ⇔
          IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))) ⇒
    ∀st res st'.
      assign_targets cx (av::gvs) (v::vs) st = (INL res,st') ⇒
      (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
      ∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        (IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) ⇔
         IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once assign_target_def, bind_def, get_Value_def, AllCaseEqs(),
       return_def, raise_def] >>
  strip_tac >> gvs[] >>
  rename1 `assign_target _ _ _ st = (INL tw, s_mid)` >>
  rename1 `get_Value tw s_mid = (INL w, s_mid2)` >>
  rename1 `assign_targets _ _ _ s_mid2 = (INL ws, st')` >>
  `s_mid = s_mid2` by (Cases_on `tw` >> gvs[get_Value_def, return_def, raise_def]) >>
  gvs[] >>
  last_x_assum (qspec_then `st` mp_tac) >> disch_then drule >> strip_tac >>
  first_x_assum (qspec_then `s_mid` mp_tac) >> disch_then drule >> strip_tac >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `IS_SOME (ALOOKUP s_mid.globals cx.txn.target)` by (first_x_assum irule >> simp[]) >>
  Cases_on `ALOOKUP s_mid.globals cx.txn.target` >> gvs[]
QED

(*
 * Combined theorem: assign_target preserves globals existence and immutables.
 * These must be proven together to avoid circular dependency in assign_targets cons case.
 * The proof uses explicit Cases_on destructuring to avoid dependence on autogenerated names.
 *)
Theorem assign_target_preserves_globals_and_immutables:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
     (∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
        IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
     (∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
        IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >-
  (* ScopedVar case: set_scopes doesn't touch globals *)
  (simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
        lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
        ignore_bind_def, set_scopes_def] >> strip_tac >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
   gvs[return_def, raise_def] >>
   rename1 `find_containing_scope _ _.scopes = SOME fcs_result` >>
   PairCases_on `fcs_result` >>
   gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   Cases_on `assign_subscripts fcs_result2 (REVERSE is) ao` >>
   gvs[return_def, raise_def] >> rw[] >> gvs[]) >-
  (* TopLevelVar case *)
  (strip_tac >>
   gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
       lookup_global_def, bind_def, get_current_globals_def, lift_option_def,
       LET_THM, set_global_def, set_current_globals_def] >>
   `st.globals = s'³'.globals ∧ ALOOKUP st.globals cx.txn.target = SOME gbs`
     by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s'³'.globals = s''.globals`
     by (Cases_on `FLOOKUP (get_module_globals src_id_opt gbs).mutables (string_to_num id)` >>
         gvs[return_def, raise_def]) >>
   `s''.globals = s'⁴'.globals`
     by (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
   Cases_on `assign_toplevel (type_env ts) tv (REVERSE is) ao` >-
   (gvs[lift_sum_def, return_def] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
         return_def, LET_THM, AllCaseEqs(), lift_option_def] >> strip_tac >> gvs[] >>
    fs[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
       return_def, LET_THM, lift_option_def] >> gvs[] >>
    conj_tac >-
    (rpt strip_tac >> Cases_on `cx.txn.target = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]) >>
    rpt strip_tac >> Cases_on `src_id_opt` >>
    simp[get_module_globals_def, set_module_globals_def, alistTheory.ALOOKUP_ADELKEY]) >>
   gvs[lift_sum_def, raise_def]) >-
  (* ImmutableVar case *)
  (strip_tac >>
   gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
       bind_def, get_current_globals_def, lift_option_def, LET_THM,
       set_immutable_def, set_current_globals_def, get_immutables_def,
       get_immutables_module_def] >>
   `st.globals = s''.globals ∧ ALOOKUP st.globals cx.txn.target = SOME gbs`
     by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s''.globals = s'⁴'.globals`
     by (Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num id)` >>
         gvs[return_def, raise_def]) >>
   Cases_on `assign_subscripts a (REVERSE is) ao` >> gvs[return_def, raise_def, lift_sum_def] >>
   qpat_x_assum `do _ od _ = _` mp_tac >>
   simp[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
        return_def, LET_THM, AllCaseEqs(), lift_option_def] >> strip_tac >> gvs[] >>
   fs[bind_def, ignore_bind_def, get_current_globals_def, set_current_globals_def,
      return_def, LET_THM, lift_option_def] >> gvs[] >>
   conj_tac >-
   (rpt strip_tac >> Cases_on `cx.txn.target = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]) >>
   simp[get_module_globals_def, set_module_globals_def, finite_mapTheory.FLOOKUP_UPDATE] >>
   rpt strip_tac >> Cases_on `string_to_num id = n` >> simp[] >>
   gvs[get_module_globals_def, return_def, raise_def, AllCaseEqs()] >>
   Cases_on `FLOOKUP (case ALOOKUP gbs NONE of NONE => empty_module_globals
                      | SOME mg => mg).immutables (string_to_num id)` >>
   gvs[return_def, raise_def]) >-
  (* TupleTargetV with TupleV - use helper lemma *)
  MATCH_ACCEPT_TAC assign_target_tuple_preserves_globals_and_immutables >-
  (* Other TupleTargetV cases - all vacuously true (raise) - 13 cases *)
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  simp[Once assign_target_def, raise_def] >-
  (* assign_targets [] [] - trivial *)
  (simp[Once assign_target_def, return_def] >> strip_tac >> gvs[] >> rw[] >> gvs[]) >-
  (* assign_targets cons case - use helper lemma *)
  MATCH_ACCEPT_TAC assign_targets_cons_preserves_globals_and_immutables >-
  (* assign_targets [] (v::vs) - vacuous *)
  simp[Once assign_target_def, raise_def] >-
  (* assign_targets (v::vs) [] - vacuous *)
  simp[Once assign_target_def, raise_def]
QED

(* Derived: assign_target preserves immutables *)
Theorem assign_target_preserves_immutables:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     ∀n gbs gbs'.
       ALOOKUP st.globals cx.txn.target = SOME gbs ∧
       ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
       IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
       IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     ∀n gbs gbs'.
       ALOOKUP st.globals cx.txn.target = SOME gbs ∧
       ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
       IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
       IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))
Proof
  metis_tac[assign_target_preserves_globals_and_immutables]
QED

(* Derived: assign_target preserves globals existence *)
Theorem assign_target_preserves_globals:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
     IS_SOME (ALOOKUP st'.globals cx.txn.target)) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
     IS_SOME (ALOOKUP st'.globals cx.txn.target))
Proof
  metis_tac[assign_target_preserves_globals_and_immutables]
QED

(**********************************************************************)

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
      by metis_tac[assign_target_preserves_scopes] >>
    `IS_SOME (ALOOKUP r.globals cx.txn.target)`
      by (drule (CONJUNCT1 assign_target_preserves_globals) >> simp[]) >>
    Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    `FLOOKUP (get_module_globals NONE x'').immutables (string_to_num n) = NONE`
      by (drule (CONJUNCT1 assign_target_preserves_immutables) >>
          disch_then (qspec_then `string_to_num n` mp_tac) >> simp[]) >>
    gvs[exactly_one_option_def, return_def]) >-
   ((* ImmutableVar case *)
    strip_tac >> gvs[] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def,
         get_current_globals_def, lift_option_def, lift_sum_def,
         immutable_target_def] >>
    `lookup_scopes (string_to_num n) r.scopes = NONE`
      by metis_tac[assign_target_preserves_scopes,
                   optionTheory.IS_SOME_DEF, optionTheory.option_CLAUSES] >>
    `IS_SOME (ALOOKUP r.globals cx.txn.target)`
      by (drule (CONJUNCT1 assign_target_preserves_globals) >> simp[]) >>
    Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    rename1 `ALOOKUP r.globals cx.txn.target = SOME gbs'` >>
    `IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables (string_to_num n))`
      by (drule (CONJUNCT1 assign_target_preserves_immutables) >>
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
     by metis_tac[assign_target_preserves_scopes] >>
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
    by (drule (CONJUNCT1 assign_target_preserves_globals) >> simp[]) >>
  Cases_on `ALOOKUP r.globals cx.txn.target` >> gvs[] >>
  rpt strip_tac >>
  `var_in_scope st n`
    by (fs[var_in_scope_def, lookup_scoped_var_def] >>
        metis_tac[CONJUNCT1 assign_target_preserves_scopes]) >>
  `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE`
    by metis_tac[] >>
  drule (CONJUNCT1 assign_target_preserves_immutables) >>
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
   metis_tac[CONJUNCT1 assign_target_preserves_scopes]) >>
  fs[assign_target_spec_def]
QED
