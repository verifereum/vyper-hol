Theory vyperAssignTargetLemmas

Ancestors
  vyperInterpreter

(*********************************************************************************)
(* Helper lemmas *)

Theorem ALOOKUP_set_module_globals_preserves[local]:
  ∀al k v tgt. IS_SOME (ALOOKUP al tgt) ⇒ IS_SOME (ALOOKUP ((k, v) :: ADELKEY k al) tgt)
Proof
  rpt strip_tac >> Cases_on `k = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]
QED

(* Helper lemma for TupleTargetV + TupleV case of the induction *)
Theorem assign_target_tuple_preserves_globals_and_immutables_dom[local]:
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
Theorem assign_targets_cons_preserves_globals_and_immutables_dom[local]:
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

Theorem assign_target_preserves_globals_and_immutables_dom[local]:
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
  MATCH_ACCEPT_TAC assign_target_tuple_preserves_globals_and_immutables_dom >-
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
  MATCH_ACCEPT_TAC assign_targets_cons_preserves_globals_and_immutables_dom >-
  (* assign_targets [] (v::vs) - vacuous *)
  simp[Once assign_target_def, raise_def] >-
  (* assign_targets (v::vs) [] - vacuous *)
  simp[Once assign_target_def, raise_def]
QED

(*********************************************************************************)
(* Main theorems  *)

Theorem assign_target_preserves_immutables_dom:
  ∀cx av ao st res st'.
    assign_target cx av ao st = (INL res, st') ⇒
    ∀n gbs gbs'.
      ALOOKUP st.globals cx.txn.target = SOME gbs ∧
      ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
      IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
      IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)
Proof
  metis_tac[assign_target_preserves_globals_and_immutables_dom]
QED

Theorem assign_targets_preserves_immutables_dom:
  ∀cx gvs vs st res st'.
    assign_targets cx gvs vs st = (INL res, st') ⇒
    ∀n gbs gbs'.
      ALOOKUP st.globals cx.txn.target = SOME gbs ∧
      ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
      IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
      IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)
Proof
  metis_tac[assign_target_preserves_globals_and_immutables_dom]
QED

Theorem assign_target_preserves_globals_dom:
  ∀cx av ao st res st'.
    assign_target cx av ao st = (INL res, st') ⇒
    IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
    IS_SOME (ALOOKUP st'.globals cx.txn.target)
Proof
  metis_tac[assign_target_preserves_globals_and_immutables_dom]
QED

Theorem assign_targets_preserves_globals_dom:
  ∀cx gvs vs st res st'.
    assign_targets cx gvs vs st = (INL res, st') ⇒
    IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
    IS_SOME (ALOOKUP st'.globals cx.txn.target)
Proof
  metis_tac[assign_target_preserves_globals_and_immutables_dom]
QED
