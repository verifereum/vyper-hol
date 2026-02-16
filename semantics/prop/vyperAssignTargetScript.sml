Theory vyperAssignTarget

Ancestors
  vyperInterpreter vyperScopePreservation vyperLookup

(*********************************************************************************)
(* Helper lemmas for immutables preservation *)

(* Helper lemma for TupleTargetV + TupleV case of the induction *)
Theorem assign_target_tuple_preserves_immutables_dom[local]:
  ∀cx gvs vs.
    (∀st res st'.
       assign_targets cx gvs vs st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
       ∀n imms imms'.
         ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
         (IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) ⇔
          IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))) ⇒
    ∀st res st'.
      assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) st = (INL res,st') ⇒
      (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
      ∀n imms imms'.
        ALOOKUP st.immutables cx.txn.target = SOME imms ∧
        ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
        (IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) ⇔
         IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once assign_target_def, check_def, AllCaseEqs(), return_def, raise_def] >>
  simp[bind_def, ignore_bind_def, assert_def, return_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Helper lemma for assign_targets cons case of the induction *)
Theorem assign_targets_cons_preserves_immutables_dom[local]:
  ∀cx av v gvs vs.
    (∀st res st'.
       assign_target cx av (Replace v) st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
       ∀n imms imms'.
         ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
         (IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) ⇔
          IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))) ∧
    (∀st res st'.
       assign_targets cx gvs vs st = (INL res,st') ⇒
       (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
       ∀n imms imms'.
         ALOOKUP st.immutables cx.txn.target = SOME imms ∧
         ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
         (IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) ⇔
          IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))) ⇒
    ∀st res st'.
      assign_targets cx (av::gvs) (v::vs) st = (INL res,st') ⇒
      (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
      ∀n imms imms'.
        ALOOKUP st.immutables cx.txn.target = SOME imms ∧
        ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
        (IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) ⇔
         IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))
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
  `IS_SOME (ALOOKUP s_mid.immutables cx.txn.target)` by (first_x_assum irule >> simp[]) >>
  Cases_on `ALOOKUP s_mid.immutables cx.txn.target` >> gvs[]
QED

Theorem assign_target_preserves_immutables_dom_main[local]:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
     (∀n imms imms'.
        ALOOKUP st.immutables cx.txn.target = SOME imms ∧
        ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
        IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) =
        IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)) ∧
     (∀n imms imms'.
        ALOOKUP st.immutables cx.txn.target = SOME imms ∧
        ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
        IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) =
        IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n)))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >-
  (* ScopedVar case: set_scopes doesn't touch immutables *)
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
  (* TopLevelVar case: storage operations don't touch immutables *)
   (strip_tac >>
    gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
        bind_def, lift_option_def, lift_sum_def, ignore_bind_def] >>
    drule lookup_global_immutables >> strip_tac >>
    Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def] >>
    Cases_on `tv` >> gvs[bind_def]
    (* Value case *)
    >- (Cases_on `assign_subscripts v (REVERSE is) ao` >> gvs[return_def, raise_def] >>
        Cases_on `set_global cx src_id_opt (string_to_num id) x s''` >> gvs[] >>
        drule set_global_immutables >> strip_tac >> gvs[return_def] >>
        Cases_on `q` >> gvs[return_def, raise_def] >> rw[] >> gvs[])
    (* HashMapRef case *)
    >> (Cases_on `REVERSE is` >> gvs[return_def, raise_def] >>
        Cases_on `split_hashmap_subscripts v t'` >> gvs[bind_def, return_def, raise_def] >>
        PairCases_on `x` >> gvs[] >>
        Cases_on `compute_hashmap_slot c (t::x1) (h::TAKE (LENGTH t' − LENGTH x2) t')` >>
        gvs[bind_def, return_def, raise_def] >>
        Cases_on `evaluate_type (get_tenv cx) x0` >> gvs[return_def, raise_def] >>
        Cases_on `read_storage_slot cx b x x' s''` >> gvs[] >>
        imp_res_tac read_storage_slot_immutables >> gvs[] >>
        Cases_on `q` >> gvs[] >>
        Cases_on `assign_subscripts x'' x2 ao` >> gvs[return_def, raise_def] >>
        Cases_on `write_storage_slot cx b x x' x'³' r` >> gvs[] >>
        imp_res_tac write_storage_slot_immutables >> gvs[] >>
        Cases_on `q` >> gvs[] >> rw[] >> gvs[])) >-
  (* ImmutableVar case: updates st.immutables, but preserves domain *)
   (strip_tac >>
    simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
         lift_option_def, LET_THM, return_def, raise_def] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[return_def, raise_def] >-
    gvs[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
        lift_option_def, LET_THM, return_def, raise_def] >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
         lift_option_def, LET_THM, return_def, raise_def] >>
    Cases_on `FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num id)` >>
    simp[return_def, raise_def] >>
    Cases_on `assign_subscripts x' (REVERSE is) ao` >> simp[lift_sum_def, return_def, raise_def] >>
    simp[ignore_bind_def, bind_def, set_immutable_def, get_address_immutables_def,
         set_address_immutables_def, lift_option_def, return_def, LET_THM] >>
    strip_tac >> gvs[] >>
    conj_tac >-
    (rpt strip_tac >> Cases_on `cx.txn.target = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]) >>
    simp[get_source_immutables_def, set_source_immutables_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    rpt strip_tac >> Cases_on `string_to_num id = n` >> simp[] >>
    gvs[get_source_immutables_def]) >-
  (* TupleTargetV with TupleV - use helper lemma *)
  MATCH_ACCEPT_TAC assign_target_tuple_preserves_immutables_dom >-
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
  MATCH_ACCEPT_TAC assign_targets_cons_preserves_immutables_dom >-
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
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) =
      IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n)
Proof
  metis_tac[assign_target_preserves_immutables_dom_main]
QED

Theorem assign_targets_preserves_immutables_dom:
  ∀cx gvs vs st res st'.
    assign_targets cx gvs vs st = (INL res, st') ⇒
    ∀n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms) n) =
      IS_SOME (FLOOKUP (get_source_immutables (current_module cx) imms') n)
Proof
  metis_tac[assign_target_preserves_immutables_dom_main]
QED

Theorem assign_target_preserves_immutables_addr_dom:
  ∀cx av ao st res st'.
    assign_target cx av ao st = (INL res, st') ⇒
    IS_SOME (ALOOKUP st.immutables cx.txn.target) ⇒
    IS_SOME (ALOOKUP st'.immutables cx.txn.target)
Proof
  metis_tac[assign_target_preserves_immutables_dom_main]
QED

(* Helper lemma for assign_targets cons case of the reverse direction *)
Theorem assign_targets_cons_preserves_immutables_addr_dom_rev[local]:
  ∀cx av v gvs vs.
    (∀st res st'.
       assign_target cx av (Replace v) st = (res,st') ⇒
       IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
       IS_SOME (ALOOKUP st.immutables cx.txn.target)) ∧
    (∀st res st'.
       assign_targets cx gvs vs st = (res,st') ⇒
       IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
       IS_SOME (ALOOKUP st.immutables cx.txn.target)) ⇒
    ∀st res st'.
      assign_targets cx (av::gvs) (v::vs) st = (res,st') ⇒
      IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
      IS_SOME (ALOOKUP st.immutables cx.txn.target)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once assign_target_def, bind_def, get_Value_def, AllCaseEqs(),
       return_def, raise_def] >>
  strip_tac >> gvs[] >>
  rename1 `assign_target _ _ _ st = (INL tgtw, s_mid)` >>
  rename1 `get_Value tgtw s_mid = (_, s_mid2)` >>
  TRY (rename1 `assign_targets _ _ _ s_mid2 = (_, st')`) >>
  `s_mid = s_mid2` by (Cases_on `tgtw` >> gvs[get_Value_def, return_def, raise_def]) >>
  gvs[] >> metis_tac[]
QED

(* Reverse direction: if st' has immutables entry, so does st *)
Theorem assign_target_preserves_immutables_addr_dom_rev:
  ∀cx av ao st res st'.
    assign_target cx av ao st = (res, st') ⇒
    IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
    IS_SOME (ALOOKUP st.immutables cx.txn.target)
Proof
  (* This is provable: assign_target can only modify immutables if get_address_immutables
     succeeds, which requires st to already have an entry. For ScopedVar and TopLevelVar,
     immutables are unchanged. For ImmutableVar, the get_address_immutables check fails
     if st doesn't have the entry. *)
  `(∀cx av ao st res st'. assign_target cx av ao st = (res, st') ⇒
      IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
      IS_SOME (ALOOKUP st.immutables cx.txn.target)) ∧
   (∀cx gvs vs st res st'. assign_targets cx gvs vs st = (res, st') ⇒
      IS_SOME (ALOOKUP st'.immutables cx.txn.target) ⇒
      IS_SOME (ALOOKUP st.immutables cx.txn.target))`
    suffices_by metis_tac[] >>
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >-
  (* ScopedVar case: set_scopes doesn't touch immutables *)
  (simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
        lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
        ignore_bind_def, set_scopes_def] >> strip_tac >> gvs[] >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
   gvs[return_def, raise_def] >>
   rename1 `find_containing_scope _ _.scopes = SOME fcs_result` >>
   PairCases_on `fcs_result` >>
   gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   Cases_on `assign_subscripts fcs_result2 (REVERSE is) ao` >>
   gvs[return_def, raise_def]) >-
  (* TopLevelVar case: storage operations don't touch immutables *)
  (strip_tac >>
   gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
       bind_def, lift_option_def, lift_sum_def, ignore_bind_def] >>
   imp_res_tac lookup_global_immutables >> gvs[] >>
   Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def] >>
   Cases_on `tv` >> gvs[bind_def]
   (* Value case *)
   >- (Cases_on `assign_subscripts v (REVERSE is) ao` >> gvs[return_def, raise_def] >>
       Cases_on `set_global cx src_id_opt (string_to_num id) x s''` >> gvs[] >>
       imp_res_tac set_global_immutables >> gvs[return_def] >>
       Cases_on `q` >> gvs[return_def, raise_def])
   (* HashMapRef case *)
   >> (Cases_on `REVERSE is` >> gvs[return_def, raise_def] >>
       Cases_on `split_hashmap_subscripts v t'` >> gvs[bind_def, return_def, raise_def] >>
       PairCases_on `x` >> gvs[] >>
       Cases_on `compute_hashmap_slot c (t::x1) (h::TAKE (LENGTH t' − LENGTH x2) t')` >>
       gvs[bind_def, return_def, raise_def] >>
       Cases_on `evaluate_type (get_tenv cx) x0` >> gvs[return_def, raise_def] >>
       Cases_on `read_storage_slot cx b x x' s''` >> gvs[] >>
       imp_res_tac read_storage_slot_immutables >> gvs[] >>
       Cases_on `q` >> gvs[] >>
       Cases_on `assign_subscripts x'' x2 ao` >> gvs[return_def, raise_def] >>
       Cases_on `write_storage_slot cx b x x' x'³' r` >> gvs[] >>
       imp_res_tac write_storage_slot_immutables >> gvs[] >>
       Cases_on `q` >> gvs[])) >-
  (* ImmutableVar case: get_address_immutables must succeed for any result.
     The goal is IS_SOME st' => IS_SOME st. If st doesn't have the entry,
     get_address_immutables raises, so either we return that error (st' = st)
     or we continue but any successful path also requires st to have the entry. *)
  (simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
        lift_option_def, LET_THM, return_def, raise_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[return_def, raise_def] >>
   BasicProvers.EVERY_CASE_TAC >>
   gvs[raise_def, return_def, lift_sum_def, AllCaseEqs(), bind_def, ignore_bind_def,
       set_immutable_def, get_address_immutables_def, lift_option_def,
       set_address_immutables_def, LET_THM] >>
   strip_tac >> gvs[]) >-
  (* TupleTargetV with TupleV - delegate to assign_targets *)
  (rpt gen_tac >> strip_tac >> rpt gen_tac >>
   simp[Once assign_target_def, check_def, AllCaseEqs(), return_def, raise_def] >>
   simp[bind_def, ignore_bind_def, assert_def, AllCaseEqs()] >>
   strip_tac >> gvs[return_def] >> first_x_assum drule >> simp[]) >-
  (* Other TupleTargetV cases - all raise (13 cases) *)
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
  simp[Once assign_target_def, return_def] >-
  (* assign_targets cons case - use helper lemma *)
  MATCH_ACCEPT_TAC assign_targets_cons_preserves_immutables_addr_dom_rev >-
  (* assign_targets [] (v::vs) - vacuous *)
  simp[Once assign_target_def, raise_def] >-
  (* assign_targets (v::vs) [] - vacuous *)
  simp[Once assign_target_def, raise_def]
QED

Theorem assign_targets_preserves_immutables_addr_dom:
  ∀cx gvs vs st res st'.
    assign_targets cx gvs vs st = (INL res, st') ⇒
    IS_SOME (ALOOKUP st.immutables cx.txn.target) ⇒
    IS_SOME (ALOOKUP st'.immutables cx.txn.target)
Proof
  metis_tac[assign_target_preserves_immutables_dom_main]
QED

(* Lemma: for ImmutableVar Replace, lookup_immutable returns the new value *)
Theorem assign_target_immutable_replace_gives_lookup:
  ∀cx st n v res st'.
    IS_SOME (lookup_immutable cx st n) ∧
    assign_target cx (BaseTargetV (ImmutableVar n) []) (Replace v) st = (INL res, st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, LET_THM, return_def] >>
  simp[lift_sum_def, assign_subscripts_def, return_def, ignore_bind_def, bind_def] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num n)` >> gvs[return_def, raise_def] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_def, bind_def,
       set_address_immutables_def, return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Lemma: for ImmutableVar Update, lookup_immutable returns the computed value *)
Theorem assign_target_immutable_update_gives_lookup:
  ∀cx st n bop v1 v2 v res st'.
    lookup_immutable cx st n = SOME v1 ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target cx (BaseTargetV (ImmutableVar n) []) (Update bop v2) st = (INL res, st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, LET_THM, return_def] >>
  simp[lift_sum_def, assign_subscripts_def, return_def, ignore_bind_def, bind_def] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_def, bind_def,
       set_address_immutables_def, return_def, LET_THM] >>
  strip_tac >> gvs[] >>
  simp[get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
