Theory vyperAssignTarget
Ancestors
  vyperMisc vyperAST vyperValue vyperValueOperation vyperState vyperInterpreter
  vyperScopePreservation vyperStatePreservation
  vyperLookup vyperLookupStorage
  vyperImmutablesPreservation vyperStorageBackend
  vyperHashMap vyperHashMapStorage

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
  simp[Once assign_target_def, check_def, type_check_def, AllCaseEqs(), return_def, raise_def] >>
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
  simp[Once assign_target_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def] >>
  strip_tac >> gvs[] >>
  rename1 `assign_target _ _ _ st = (INL _, s_mid)` >>
  rename1 `assign_targets _ _ _ s_mid = (INL _, st')` >>
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
        lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
        ignore_bind_def, set_scopes_def] >> strip_tac >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
   gvs[return_def, raise_def] >>
   rename1 `find_containing_scope _ _.scopes = SOME fcs_result` >>
   PairCases_on `fcs_result` >>
   gvs[bind_def, type_check_def, assert_def, sum_CASE_rator, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   Cases_on `assign_subscripts fcs_result2.type fcs_result2.value (REVERSE is) ao` >>
   gvs[return_def, raise_def] >> rw[] >> gvs[] >>
   imp_res_tac assign_result_state >> gvs[] >> rw[] >> gvs[]) >-
  (* TopLevelVar case: storage operations don't touch immutables *)
   (strip_tac >>
    gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
        bind_def, lift_option_def, lift_option_type_def, lift_sum_def,
        ignore_bind_def,
        option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
    drule lookup_global_immutables >> strip_tac >>
    qpat_x_assum `_ = (INL res, st')` mp_tac >>
    simp[bind_def, return_def, raise_def, ignore_bind_def,
         lift_option_def, lift_option_type_def, lift_sum_def,
         check_def, assert_def,
         option_CASE_rator, prod_CASE_rator, sum_CASE_rator,
         type_value_CASE_rator, toplevel_value_CASE_rator,
         assign_operation_CASE_rator, bound_CASE_rator,
         AllCaseEqs(), PULL_EXISTS] >>
    rpt strip_tac >>
    TRY (pairarg_tac >> gvs[bind_def, return_def, raise_def,
        AllCaseEqs(), option_CASE_rator, prod_CASE_rator, sum_CASE_rator,
        type_value_CASE_rator, assign_operation_CASE_rator, bound_CASE_rator,
        check_def, assert_def, ignore_bind_def,
        lift_option_def, lift_option_type_def, lift_sum_def, PULL_EXISTS] >>
      rpt strip_tac) >>
    MAP_EVERY (fn th => TRY (imp_res_tac th >> gvs[]))
      [assign_result_state, set_global_immutables,
       resolve_array_element_state,
       read_storage_slot_immutables, write_storage_slot_immutables,
       get_storage_backend_state]) >-
  (* ImmutableVar case: updates st.immutables, but preserves domain *)
   (strip_tac >>
    simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
         lift_option_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[return_def, raise_def] >-
    gvs[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
        lift_option_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
         lift_option_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
    Cases_on `FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num id)` >>
    simp[return_def, raise_def] >>
    PairCases_on `x'` >>
    simp[] >>
    Cases_on `assign_subscripts x'0 x'1 (REVERSE is) ao` >> simp[lift_sum_def, return_def, raise_def] >>
    simp[ignore_bind_def, bind_def, set_immutable_def, get_address_immutables_def,
         set_address_immutables_def, lift_option_def, lift_option_type_def, return_def, LET_THM] >>
    strip_tac >> gvs[] >>
    imp_res_tac assign_result_state >> gvs[] >>
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
  simp[Once assign_target_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def] >>
  strip_tac >> gvs[]
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
        lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
        ignore_bind_def, set_scopes_def] >> strip_tac >> gvs[] >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
   gvs[return_def, raise_def] >>
   rename1 `find_containing_scope _ _.scopes = SOME fcs_result` >>
   PairCases_on `fcs_result` >>
   gvs[bind_def, type_check_def, assert_def, sum_CASE_rator, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   Cases_on `assign_subscripts fcs_result2.type fcs_result2.value (REVERSE is) ao` >>
   gvs[return_def, raise_def] >>
   imp_res_tac assign_result_state >> gvs[]) >-
  (* TopLevelVar case: storage operations don't touch immutables *)
  (strip_tac >>
   gvs[Once assign_target_def, AllCaseEqs(), return_def, raise_def,
       bind_def, lift_option_def, lift_option_type_def, lift_sum_def, ignore_bind_def,
       option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
   drule lookup_global_immutables >> strip_tac >>
   qpat_x_assum `_ = (res, st')` mp_tac >>
   simp[bind_def, return_def, raise_def, ignore_bind_def,
        lift_option_def, lift_option_type_def, lift_sum_def,
        check_def, assert_def,
        option_CASE_rator, prod_CASE_rator, sum_CASE_rator,
        type_value_CASE_rator, toplevel_value_CASE_rator,
        assign_operation_CASE_rator, bound_CASE_rator,
        AllCaseEqs(), PULL_EXISTS] >>
   rpt strip_tac >>
   gvs[pairTheory.ELIM_UNCURRY, bind_def, return_def, raise_def,
       ignore_bind_def, lift_option_def, lift_option_type_def, lift_sum_def,
       check_def, assert_def,
       option_CASE_rator, prod_CASE_rator, sum_CASE_rator,
       type_value_CASE_rator, assign_operation_CASE_rator, bound_CASE_rator,
       AllCaseEqs(), PULL_EXISTS] >>
   MAP_EVERY (fn th => TRY (imp_res_tac th >> gvs[]))
     [assign_result_state, set_global_immutables,
      resolve_array_element_state,
      read_storage_slot_immutables, write_storage_slot_immutables,
      get_storage_backend_state]) >-
  (* ImmutableVar case: get_address_immutables must succeed for any result.
     The goal is IS_SOME st' => IS_SOME st. If st doesn't have the entry,
     get_address_immutables raises, so either we return that error (st' = st)
     or we continue but any successful path also requires st to have the entry. *)
  (simp[Once assign_target_def, bind_def, get_immutables_def, get_address_immutables_def,
        lift_option_def, lift_option_type_def, LET_THM, return_def, raise_def] >>
   Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[return_def, raise_def] >>
   BasicProvers.EVERY_CASE_TAC >>
   gvs[raise_def, return_def, lift_sum_def, AllCaseEqs(), bind_def, ignore_bind_def,
       set_immutable_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       set_address_immutables_def, LET_THM] >>
   strip_tac >> gvs[]) >-
  (* TupleTargetV with TupleV - delegate to assign_targets *)
  (rpt gen_tac >> strip_tac >> rpt gen_tac >>
   simp[Once assign_target_def, check_def, type_check_def, AllCaseEqs(), return_def, raise_def] >>
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

Theorem assign_target_toplevel_update:
  ∀cx st src_id_opt n ty bop v1 v2 v.
    lookup_toplevel_name cx st src_id_opt n = SOME (Value v1) ∧
    evaluate_binop
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u)
      NoneTV bop v1 v2 = INL v ∧
    var_in_storage cx src_id_opt n ∧
    storable_value cx src_id_opt n v ⇒
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt n) []) (Update ty bop v2) st =
    (INL NONE, update_toplevel_name cx st src_id_opt n v)
Proof
  rw[var_in_storage_def] >>
  gvs[lookup_toplevel_name_def, AllCaseEqs()] >>
  `st' = st` by metis_tac[lookup_global_state] >> gvs[] >>
  `storage_type_of cx src_id_opt n = SOME tv` by
    simp[storage_type_of_def, storage_var_info_def] >>
  `value_has_type tv v` by
    (gvs[storable_value_def] >> first_x_assum drule >> simp[]) >>
  `IS_SOME (encode_value tv v)` by
    metis_tac[CONJUNCT1 vyperTypingTheory.value_has_type_equiv] >>
  Cases_on `encode_value tv v` >> gvs[] >>
  `∃storage. get_storage_backend cx b st = (INL storage, st)` by
    metis_tac[get_storage_backend_INL] >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       listTheory.REVERSE_DEF, lift_option_type_def, optionTheory.OPTION_BIND_def,
       assign_subscripts_def, lift_sum_def,
       ignore_bind_def, assign_result_def] >>
  gvs[AllCaseEqs()] >>
  `ISL (FST (set_global cx src_id_opt (string_to_num n) v st))` by (
    simp[Once set_global_def, bind_def, return_def, LET_THM,
         lift_option_type_def, write_storage_slot_def, lift_option_def] >>
    Cases_on `b` >>
    gvs[set_storage_backend_def, bind_def, return_def,
        update_transient_def, get_accounts_def, update_accounts_def, LET_THM]) >>
  Cases_on `set_global cx src_id_opt (string_to_num n) v st` >>
  Cases_on `q` >> gvs[update_toplevel_name_def]
QED

Theorem assign_target_toplevel_replace:
  ∀cx st src_id_opt n v v0.
    lookup_toplevel_name cx st src_id_opt n = SOME (Value v0) ∧
    var_in_storage cx src_id_opt n ∧
    storable_value cx src_id_opt n v ⇒
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt n) []) (Replace v) st =
    (INL NONE, update_toplevel_name cx st src_id_opt n v)
Proof
  rw[var_in_storage_def] >>
  gvs[lookup_toplevel_name_def, AllCaseEqs()] >>
  `st' = st` by metis_tac[lookup_global_state] >> gvs[] >>
  `storage_type_of cx src_id_opt n = SOME tv` by
    simp[storage_type_of_def, storage_var_info_def] >>
  `value_has_type tv v` by
    (gvs[storable_value_def] >> first_x_assum drule >> simp[]) >>
  `IS_SOME (encode_value tv v)` by
    metis_tac[CONJUNCT1 vyperTypingTheory.value_has_type_equiv] >>
  Cases_on `encode_value tv v` >> gvs[] >>
  `∃storage. get_storage_backend cx b st = (INL storage, st)` by
    metis_tac[get_storage_backend_INL] >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       listTheory.REVERSE_DEF, lift_option_type_def, optionTheory.OPTION_BIND_def,
       assign_subscripts_def, lift_sum_def,
       ignore_bind_def, assign_result_def] >>
  gvs[AllCaseEqs()] >>
  `ISL (FST (set_global cx src_id_opt (string_to_num n) v st))` by (
    simp[Once set_global_def, bind_def, return_def, LET_THM,
         lift_option_type_def, write_storage_slot_def, lift_option_def] >>
    Cases_on `b` >>
    gvs[set_storage_backend_def, bind_def, return_def,
        update_transient_def, get_accounts_def, update_accounts_def, LET_THM]) >>
  Cases_on `set_global cx src_id_opt (string_to_num n) v st` >>
  Cases_on `q` >> gvs[update_toplevel_name_def]
QED

(* ===== HashMap assign_target bridge lemmas ===== *)

(* Depth-1: assign_target for leaf HashMap with Replace *)
Theorem assign_target_leaf_replace:
  ∀cx st src_id_opt n key kv v cur.
    is_leaf_hashmap cx src_id_opt n ∧
    value_to_key kv = SOME key ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st src_id_opt n)) v ∧
    lookup_hashmap cx st src_id_opt n kv = SOME cur ⇒
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt n) [key]) (Replace v) st =
    (INL NONE, update_hashmap cx st src_id_opt n kv v)
Proof
  rw[is_leaf_hashmap_def] >>
  `lookup_global cx src_id_opt (string_to_num n) st =
   (INL (HashMapRef is_transient (n2w offset) kt (Type t)), st)` by
    (simp[Once lookup_global_def, bind_def, return_def, LET_THM,
          lift_option_type_def, raise_def]) >>
  `lookup_toplevel_name cx st src_id_opt n =
   SOME (HashMapRef is_transient (n2w offset) kt (Type t))` by
    (simp[lookup_toplevel_name_def]) >>
  gvs[lookup_hashmap_def, read_hashmap_def, hashmap_read_def] >>
  drule_at (Pos last) encode_hashmap_key_value_to_key >>
  disch_then (qspec_then `kt` strip_assume_tac) >>
  `value_has_type tv v` by gvs[hashmap_ref_storable_def] >>
  `∃writes. encode_value tv v = SOME writes` by
    (`∃s'. hashmap_write (get_storage cx st is_transient) (n2w offset)
           kt tv kv v = SOME s'` by (irule hashmap_write_some >> simp[]) >>
     gvs[hashmap_write_def, AllCaseEqs()]) >>
  `compute_hashmap_slot (n2w offset) [kt] [key] =
   SOME (hashmap_slot_for (n2w offset) kt kv)` by
    (drule compute_hashmap_slot_single >>
     simp[hashmap_slot_for_def]) >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       lift_option_type_def, raise_def,
       split_hashmap_subscripts_type, lift_sum_def,
       assign_subscripts_def, assign_result_def,
       read_storage_slot_eq, write_storage_slot_eq] >>
  simp[Once ignore_bind_def, bind_def, return_def,
       write_storage_slot_eq,
       update_hashmap_def, write_hashmap_def,
       hashmap_write_def, hashmap_slot_for_def]
QED

(* Depth-1: assign_target for leaf HashMap with Update *)
Theorem assign_target_leaf_update:
  ∀cx st src_id_opt n key kv v v_old v_new ty bop.
    is_leaf_hashmap cx src_id_opt n ∧
    value_to_key kv = SOME key ∧
    lookup_hashmap cx st src_id_opt n kv = SOME v_old ∧
    evaluate_binop
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u)
      NoneTV bop v_old v = INL v_new ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st src_id_opt n)) v_new ⇒
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt n) [key]) (Update ty bop v) st =
    (INL NONE, update_hashmap cx st src_id_opt n kv v_new)
Proof
  rw[is_leaf_hashmap_def] >>
  `lookup_global cx src_id_opt (string_to_num n) st =
   (INL (HashMapRef is_transient (n2w offset) kt (Type t)), st)` by
    (simp[Once lookup_global_def, bind_def, return_def, LET_THM,
          lift_option_type_def, raise_def]) >>
  `lookup_toplevel_name cx st src_id_opt n =
   SOME (HashMapRef is_transient (n2w offset) kt (Type t))` by
    (simp[lookup_toplevel_name_def]) >>
  gvs[lookup_hashmap_def, read_hashmap_def, hashmap_read_def] >>
  drule_at (Pos last) encode_hashmap_key_value_to_key >>
  disch_then (qspec_then `kt` strip_assume_tac) >>
  `value_has_type tv v_new` by gvs[hashmap_ref_storable_def] >>
  `∃writes. encode_value tv v_new = SOME writes` by
    (`∃s'. hashmap_write (get_storage cx st is_transient) (n2w offset)
           kt tv kv v_new = SOME s'` by (irule hashmap_write_some >> simp[]) >>
     gvs[hashmap_write_def, AllCaseEqs()]) >>
  `compute_hashmap_slot (n2w offset) [kt] [key] =
   SOME (hashmap_slot_for (n2w offset) kt kv)` by
    (drule compute_hashmap_slot_single >>
     simp[hashmap_slot_for_def]) >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       lift_option_type_def, raise_def,
       split_hashmap_subscripts_type, lift_sum_def,
       assign_subscripts_def, assign_result_def,
       read_storage_slot_eq, write_storage_slot_eq] >>
  simp[Once ignore_bind_def, bind_def, return_def,
       write_storage_slot_eq,
       update_hashmap_def, write_hashmap_def,
       hashmap_write_def, hashmap_slot_for_def]
QED

(* General bridge: assign_target for HashMap with Replace *)
Theorem assign_target_hashmap_replace:
  ∀cx st src_id_opt n sbs href0 keys href_leaf last_kv v cur.
    (∀st. lookup_toplevel_name cx st src_id_opt n = SOME href0) ∧
    subscripts_to_values (REVERSE sbs) = SOME (keys ++ [last_kv]) ∧
    hashmap_index_chain href0 keys = SOME href_leaf ∧
    is_leaf_hashmap_ref cx href_leaf ∧
    read_hashmap cx st href_leaf last_kv = SOME cur ∧
    hashmap_ref_storable cx href_leaf v ⇒
    ∃r. assign_target cx
      (BaseTargetV (TopLevelVar src_id_opt n) sbs) (Replace v) st =
    (INL r, write_hashmap cx st href_leaf last_kv v)
Proof
  rw[] >>
  first_assum (strip_assume_tac o Q.SPEC `st`) >>
  imp_res_tac lookup_toplevel_name_lookup_global >>
  imp_res_tac lookup_global_get_module_code >>
  Cases_on `href0` >| [
    Cases_on `keys` >> gvs[hashmap_index_chain_def, hashmap_index_def,
                            is_leaf_hashmap_ref_def],
    all_tac,
    Cases_on `keys` >> gvs[hashmap_index_chain_def, hashmap_index_def,
                            is_leaf_hashmap_ref_def]
  ] >>
  rename1 `HashMapRef is_t base_slot kt vt` >>
  drule_at (Pos last) hashmap_chain_split_compute >>
  disch_then (qspecl_then [`vt`, `is_t`, `base_slot`, `kt`, `cx`,
    `href_leaf`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[read_hashmap_def, hashmap_read_def] >>
  gvs[hashmap_ref_storable_def] >>
  rename1 `value_has_type tv_leaf v` >>
  imp_res_tac hashmap_write_some >>
  gvs[hashmap_write_def, AllCaseEqs()] >>
  `∃rsb_h rsb_t. REVERSE sbs = rsb_h :: rsb_t` by
    (Cases_on `REVERSE sbs` >> gvs[subscripts_to_values_def]) >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       lift_option_type_def, raise_def] >>
  gvs[listTheory.TAKE_LENGTH_ID] >>
  simp[assign_subscripts_def, assign_result_def, return_def,
       read_storage_slot_eq, bind_def] >>
  simp[lift_sum_def, Once ignore_bind_def, bind_def, return_def,
       write_storage_slot_eq,
       write_hashmap_def, hashmap_write_def, hashmap_slot_for_def]
QED

(* General bridge: assign_target for HashMap with Update *)
Theorem assign_target_hashmap_update:
  ∀cx st src_id_opt n sbs href0 keys href_leaf last_kv v v_old v_new ty bop.
    (∀st. lookup_toplevel_name cx st src_id_opt n = SOME href0) ∧
    subscripts_to_values (REVERSE sbs) = SOME (keys ++ [last_kv]) ∧
    hashmap_index_chain href0 keys = SOME href_leaf ∧
    is_leaf_hashmap_ref cx href_leaf ∧
    read_hashmap cx st href_leaf last_kv = SOME v_old ∧
    evaluate_binop
      (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u)
      NoneTV bop v_old v = INL v_new ∧
    hashmap_ref_storable cx href_leaf v_new ⇒
    ∃r. assign_target cx
      (BaseTargetV (TopLevelVar src_id_opt n) sbs) (Update ty bop v) st =
    (INL r, write_hashmap cx st href_leaf last_kv v_new)
Proof
  rw[] >>
  first_assum (strip_assume_tac o Q.SPEC `st`) >>
  imp_res_tac lookup_toplevel_name_lookup_global >>
  imp_res_tac lookup_global_get_module_code >>
  Cases_on `href0` >| [
    Cases_on `keys` >> gvs[hashmap_index_chain_def, hashmap_index_def,
                            is_leaf_hashmap_ref_def],
    all_tac,
    Cases_on `keys` >> gvs[hashmap_index_chain_def, hashmap_index_def,
                            is_leaf_hashmap_ref_def]
  ] >>
  rename1 `HashMapRef is_t base_slot kt vt` >>
  drule_at (Pos last) hashmap_chain_split_compute >>
  disch_then (qspecl_then [`vt`, `is_t`, `base_slot`, `kt`, `cx`,
    `href_leaf`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[read_hashmap_def, hashmap_read_def] >>
  gvs[hashmap_ref_storable_def] >>
  rename1 `value_has_type tv_leaf v_new` >>
  imp_res_tac hashmap_write_some >>
  gvs[hashmap_write_def, AllCaseEqs()] >>
  `∃rsb_h rsb_t. REVERSE sbs = rsb_h :: rsb_t` by
    (Cases_on `REVERSE sbs` >> gvs[subscripts_to_values_def]) >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       lift_option_type_def, raise_def] >>
  gvs[listTheory.TAKE_LENGTH_ID] >>
  simp[assign_subscripts_def, assign_result_def, return_def,
       read_storage_slot_eq, bind_def] >>
  simp[lift_sum_def, Once ignore_bind_def, bind_def, return_def,
       write_storage_slot_eq,
       write_hashmap_def, hashmap_write_def, hashmap_slot_for_def]
QED
