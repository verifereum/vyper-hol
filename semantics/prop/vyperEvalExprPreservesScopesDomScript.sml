Theory vyperEvalExprPreservesScopesDom

Ancestors
  vyperInterpreter vyperLookup vyperScopePreservation vyperScopePreservingExpr

Theorem eval_exprs_preserves_scopes_dom_helper[local]:
  ∀es cx st res st'.
    (∀e. MEM e es ⇒ ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  Induct >> simp[evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def, get_Value_def] >>
  imp_res_tac get_Value_scopes >> gvs[]
  (* Subgoal 1: success for h, success for es *)
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INL vs`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e`, `res`] >> simp[])
  (* Subgoal 2: success for h, error for es *)
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INR e`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e'`, `res`] >> simp[])
  (* Subgoal 3 & 4: eval_expr or get_Value on h returns error *)
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
QED

(* ========================================================================
   Helper lemmas for individual eval_base_target cases (for mutual induction)
   ======================================================================== *)

(* NameTarget case - does not call eval_expr *)
Theorem case_NameTarget_dom[local]:
  ∀cx nm st res st'.
    eval_base_target cx (NameTarget nm) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       get_scopes_def, lift_sum_def] >>
  IF_CASES_TAC >> gvs[return_def, bind_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_immutables_scopes >> gvs[]
  (* is_creation = T: involves get_immutables call *)
  >- (Cases_on `get_immutables cx NONE st` >> Cases_on `q` >> gvs[] >>
      imp_res_tac get_immutables_scopes >> gvs[] >>
      Cases_on `exactly_one_option
                  (if IS_SOME (lookup_scopes (string_to_num nm) st.scopes) then
                     SOME (ScopedVar nm) else NONE)
                  (immutable_target x nm (string_to_num nm))` >> gvs[return_def, raise_def])
  >- (Cases_on `get_immutables cx NONE st` >> Cases_on `q` >> gvs[] >>
      imp_res_tac get_immutables_scopes >> gvs[] >>
      Cases_on `exactly_one_option
                  (if IS_SOME (lookup_scopes (string_to_num nm) st.scopes) then
                     SOME (ScopedVar nm) else NONE)
                  (immutable_target x nm (string_to_num nm))` >> gvs[return_def, raise_def])
  >- (Cases_on `get_immutables cx NONE st` >> Cases_on `q` >> gvs[] >>
      imp_res_tac get_immutables_scopes >> gvs[])
  (* is_creation = F: trivial return NONE case *)
  >> Cases_on `exactly_one_option
                 (if IS_SOME (lookup_scopes (string_to_num nm) st.scopes) then
                    SOME (ScopedVar nm) else NONE) NONE` >> gvs[return_def, raise_def]
QED

(* TopLevelNameTarget case - does not call eval_expr *)
Theorem case_TopLevelNameTarget_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

(* ========================================================================
   Helper lemmas for structural induction

   The structural induction gives us predicates P0, P1, P2, P3, P4 where:
   - scopes_P0 e = ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
   - scopes_P1 bt = ∀cx st res st'. eval_base_target cx bt st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
   - scopes_P2 kes = ∀e. MEM e (MAP SND kes) ⇒ scopes_P0 e
   - scopes_P4 es = ∀e. MEM e es ⇒ scopes_P0 e

   The helper lemmas are formulated to match what we get after
   unfolding the predicates in each induction case.
   ======================================================================== *)

(* IfExp: P0 e ∧ P0 e0 ∧ P0 e1 ⇒ P0 (IfExp e e0 e1)
   After unfolding scopes_P0, the IHs have ∀cx INSIDE, not outside *)
Theorem case_IfExp_ind[local]:
  ∀e e0 e1.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e0 st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e1 st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (IfExp e e0 e1) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (IfExp _ _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def] >>
  strip_tac >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by metis_tac[] >>
  Cases_on `tv = Value (BoolV T)` >> gvs[]
  >- metis_tac[]
  >- (Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >> metis_tac[])
QED

(* Subscript: P0 e ∧ P0 e0 ⇒ P0 (Subscript e e0) *)
Theorem case_Subscript_ind[local]:
  ∀e e0.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e0 st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Subscript e e0) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum (qspec_then `cx` drule) >> simp[])) >>
  TRY (first_x_assum (qspec_then `cx` drule) >> simp[] >> strip_tac) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >> gvs[] >>
  (* Handle storage slot access case (evaluate_subscript returns INR) *)
  TRY (
    Cases_on `res'` >> gvs[return_def, bind_def, AllCaseEqs()] >>
    PairCases_on `y` >> gvs[bind_def, AllCaseEqs(), lift_option_def, return_def, raise_def] >>
    imp_res_tac read_storage_slot_scopes >> gvs[] >>
    Cases_on `evaluate_type (type_env ts) y2` >> gvs[return_def, raise_def]
  ) >> metis_tac[]
QED

(* Attribute: P0 e ⇒ ∀s. P0 (Attribute e s) *)
Theorem case_Attribute_ind[local]:
  ∀e.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀s cx st res st'.
      eval_expr cx (Attribute e s) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, get_Value_def, lift_option_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum (qspec_then `cx` drule) >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

(* SubscriptTarget: P1 b ∧ P0 e ⇒ P1 (SubscriptTarget b e) *)
Theorem case_SubscriptTarget_ind[local]:
  ∀b e.
    (∀cx st res st'. eval_base_target cx b st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_base_target cx (SubscriptTarget b e) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum (qspec_then `cx` drule) >> simp[]) >>
  first_x_assum (qspec_then `cx` drule) >> simp[]
QED

(* AttributeTarget: P1 b ⇒ ∀s. P1 (AttributeTarget b s) *)
Theorem case_AttributeTarget_ind[local]:
  ∀b.
    (∀cx st res st'. eval_base_target cx b st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀s cx st res st'.
      eval_base_target cx (AttributeTarget b s) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  first_x_assum (qspec_then `cx` drule) >> simp[]
QED

(* Pop: P1 b ⇒ P0 (Pop b) *)
Theorem case_Pop_ind[local]:
  ∀b.
    (∀cx st res st'. eval_base_target cx b st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Pop b) st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def]
  (* INL case - eval_base_target succeeded *)
  >- (PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac (CONJUNCT1 assign_target_preserves_scopes_dom) >> gvs[] >>
      imp_res_tac get_Value_scopes >> gvs[] >>
      imp_res_tac lift_sum_scopes >> gvs[] >>
      imp_res_tac lift_option_scopes >> gvs[] >>
      first_x_assum (qspec_then `cx` drule) >> gvs[])
  (* INR case - eval_base_target failed, trivial *)
  >- (first_x_assum (qspec_then `cx` drule) >> gvs[])
QED

(* StructLit: P2 l ⇒ ∀p. P0 (StructLit p l)
   After unfolding: (∀e. MEM e (MAP SND kes) ⇒ scopes_P0 e) ⇒ scopes_P0 (StructLit p kes)
   Then scopes_P0 unfolds with ∀cx inside
   Note: p must be destructured to (src_id_opt, id) for evaluate_def to apply *)
Theorem case_StructLit_ind[local]:
  ∀kes.
    (∀e. MEM e (MAP SND kes) ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀src_id_opt id cx st res st'.
      eval_expr cx (StructLit (src_id_opt, id) kes) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  drule_all eval_exprs_preserves_scopes_dom_helper >> simp[]
QED

(* Builtin: P4 l ⇒ ∀b. P0 (Builtin b l) *)
Theorem case_Builtin_ind[local]:
  ∀es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀bt cx st res st'.
      eval_expr cx (Builtin bt es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, get_accounts_def, lift_sum_def]
  >- (TRY (Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]) >>
      drule_all eval_exprs_preserves_scopes_dom_helper >> simp[])
  >- (drule_all eval_exprs_preserves_scopes_dom_helper >> simp[] >>
      Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def])
  >- (drule_all eval_exprs_preserves_scopes_dom_helper >> simp[])
QED

(* TypeBuiltin: P4 l ⇒ ∀t t0. P0 (TypeBuiltin t0 t l) *)
Theorem case_TypeBuiltin_ind[local]:
  ∀es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀tb typ cx st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]) >>
  drule_all eval_exprs_preserves_scopes_dom_helper >> simp[]
QED

(* Call: P4 l ⇒ ∀c. P0 (Call c l)
   Need to case split on c (Send, ExtCall, StaticCall, IntCall) *)
Theorem case_Call_Send_ind[local]:
  ∀es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Call Send es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, assert_def, lift_option_def] >>
  strip_tac >> gvs[return_def, raise_def, GSYM lift_option_def] >>
  imp_res_tac transfer_value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  drule_all eval_exprs_preserves_scopes_dom_helper >> simp[]
QED

Theorem case_Call_IntCall_ind[local]:
  ∀es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀src_id_opt fn cx st res st'.
      eval_expr cx (Call (IntCall (src_id_opt, fn)) es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, assert_def, lift_option_def, get_scopes_def, push_function_def,
       pop_function_def, set_scopes_def] >>
  strip_tac >> gvs[return_def, raise_def, GSYM lift_option_def] >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  TRY (drule_all finally_set_scopes_dom >> strip_tac >> gvs[]) >>
  TRY (drule_all eval_exprs_preserves_scopes_dom_helper >> simp[])
QED

Theorem case_Call_ExtCall_ind[local]:
  ∀es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀is_static sig cx st res st'.
      eval_expr cx (Call (ExtCall is_static sig) es) st = (res,st') ⇒ 
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  PairCases_on `sig` >>
  simp[evaluate_def, bind_def, ignore_bind_def, CaseEq"prod", CaseEq"sum",
       lift_option_def, CaseEq"option", option_CASE_rator, raise_def,
       return_def, check_def, assert_def, COND_RATOR,
       get_transient_storage_def, get_accounts_def, CaseEq"bool", pairTheory.UNCURRY] >>
  strip_tac >> gvs[return_def, raise_def] >>
  drule_all eval_exprs_preserves_scopes_dom_helper >> strip_tac >> gvs[] >>
  rename1 `run_ext_call _ _ _ _ _ _ _ _ = SOME result` >>
  PairCases_on `result` >>
  gvs[bind_def, ignore_bind_def, assert_def, CaseEq"prod", CaseEq"sum",
      lift_sum_def, update_accounts_def, update_transient_def, return_def,
      sum_CASE_rator, raise_def]
QED

(* ========================================================================
   Preservation Theorem proved by structural induction on expr/base_target types
   ======================================================================== *)

(* Predicates for structural induction *)
Definition scopes_P0_def[local]:
  scopes_P0 e = ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
End

Definition scopes_P1_def[local]:
  scopes_P1 bt = ∀cx st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
End

Definition scopes_P2_def[local]:
  scopes_P2 kes = ∀e. MEM e (MAP SND kes) ⇒ scopes_P0 e
End

Definition scopes_P3_def[local]:
  scopes_P3 ke = scopes_P0 (SND ke)
End

Definition scopes_P4_def[local]:
  scopes_P4 es = ∀e. MEM e es ⇒ scopes_P0 e
End

Theorem eval_mutual_preserves_scopes_dom[local]:
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  sg `(∀e:expr. scopes_P0 e) ∧ (∀bt:base_assignment_target. scopes_P1 bt) ∧
      (∀kes:(string#expr)list. scopes_P2 kes) ∧
      (∀ke:string#expr. scopes_P3 ke) ∧ (∀es:expr list. scopes_P4 es)`
  >- (ho_match_mp_tac (TypeBase.induction_of ``:expr``) >> rpt conj_tac >>
      simp[scopes_P0_def, scopes_P1_def, scopes_P2_def, scopes_P3_def, scopes_P4_def]
      (* Case 1: Name *)
      >- (rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs()] >>
          imp_res_tac get_scopes_id >> imp_res_tac get_immutables_scopes >>
          imp_res_tac lift_sum_scopes >> imp_res_tac return_scopes >> gvs[])
      (* Case 2: TopLevelName *)
      >- (rpt gen_tac >> PairCases_on `ke` >> rpt strip_tac >>
          gvs[evaluate_def] >>
          imp_res_tac lookup_global_scopes >> gvs[])
      (* Case 3: FlagMember *)
      >- (rpt gen_tac >> PairCases_on `ke` >> rpt strip_tac >>
          gvs[evaluate_def] >> imp_res_tac lookup_flag_mem_scopes >> gvs[])
      (* Case 4: IfExp *)
      >- (rpt strip_tac >> irule case_IfExp_ind >> gvs[] >>
          qexistsl_tac [`cx`, `e`, `e0`, `e1`, `res`] >> gvs[] >>
          rpt conj_tac >> first_x_assum ACCEPT_TAC)
      (* Case 5: Literal *)
      >- (rpt strip_tac >> gvs[evaluate_def, return_def])
      (* Case 6: StructLit *)
      >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> PairCases_on `ke` >> strip_tac >>
          irule case_StructLit_ind >>
          qexistsl_tac [`cx`, `ke1`, `kes`, `res`, `ke0`] >> gvs[] >>
          first_x_assum ACCEPT_TAC)
      (* Case 7: Subscript *)
      >- (rpt strip_tac >> drule_all case_Subscript_ind >> simp[])
      (* Case 8: Attribute *)
      >- (rpt strip_tac >> drule_all case_Attribute_ind >> simp[])
      (* Case 9: Builtin *)
      >- (rpt strip_tac >> drule_all case_Builtin_ind >> simp[])
      (* Case 10: TypeBuiltin *)
      >- (rpt strip_tac >> drule_all case_TypeBuiltin_ind >> simp[])
      (* Case 11: Pop *)
      >- (rpt strip_tac >> drule_all case_Pop_ind >> simp[])
      (* Case 12: Call *)
      >- (rpt strip_tac >> Cases_on `c`
          >- (PairCases_on `p` >> drule_all case_Call_IntCall_ind >> simp[])
          >- (PairCases_on `p` >> drule_all case_Call_ExtCall_ind >> simp[])
          >- (drule_all case_Call_Send_ind >> simp[]))
      (* Case 13: NameTarget *)
      >- (rpt strip_tac >> drule case_NameTarget_dom >> simp[])
      (* Case 14: TopLevelNameTarget *)
      >- (rpt gen_tac >> PairCases_on `ke` >> rpt strip_tac >>
          drule case_TopLevelNameTarget_dom >> simp[])
      (* Case 15: SubscriptTarget *)
      >- (rpt strip_tac >> drule_all case_SubscriptTarget_ind >> simp[])
      (* Case 16: AttributeTarget *)
      >- (rpt strip_tac >> drule_all case_AttributeTarget_ind >> simp[])
      (* Case 17: P2 cons *)
      >- (rpt strip_tac >> gvs[] >> metis_tac[])
      (* Case 18: P4 cons *)
      >- (rpt strip_tac >> gvs[] >> metis_tac[]))
  >> gvs[scopes_P0_def, scopes_P1_def] >> metis_tac[]
QED

(* ========================================================================
   Main theorems
   ======================================================================== *)

Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_var_in_scope:
  ∀cx st st' n e res.
    eval_expr cx e st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_expr_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_scopes_len:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_expr_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_base_target_preserves_scopes_dom:
  ∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_base_target_preserves_var_in_scope:
  ∀cx st st' n bt res.
    eval_base_target cx bt st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_base_target_preserves_scopes_dom]
QED

Theorem eval_base_target_preserves_scopes_len:
  ∀bt cx st res st'.
    eval_base_target cx bt st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_base_target_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_exprs_preserves_scopes_dom:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_exprs_preserves_scopes_dom_helper, eval_expr_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_var_in_scope:
  ∀cx st st' n es res.
    eval_exprs cx es st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_exprs_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_scopes_len:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED
