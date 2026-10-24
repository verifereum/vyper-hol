Theory vyperEvalExprPreservesScopesDom
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperCreate vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperCallOutcome[ignore_grammar]

(* ========================================================================
   Utility: eval_exprs preserves scopes dom from per-element IH
   (kept for downstream use)
   ======================================================================== *)

Theorem eval_exprs_preserves_scopes_dom_helper[local]:
  ∀es cx st res st'.
    (∀e. MEM e es ⇒ ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  Induct >> simp[evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_scopes >> gvs[]
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INL vs`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e`, `res`] >> simp[])
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INR e`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e'`, `res`] >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
QED

(* Domain preservation follows the canonical ten-function induction.
   Statements are deliberately unconstrained: declarations add locals. *)
Theorem Send_outcome_preserves_locals:
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  drule_all (Send_outcome_transport |> Q.INST
    [`R` |-> `\s t. t.scopes = s.scopes /\ t.immutables = s.immutables`]
    |> SRULE []) >> simp[]
QED

Theorem eval_mutual_preserves_scopes_dom[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def,
          lift_option_type_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_flag_mem_scopes >> gvs[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `builtin_args_length_ok bt (LENGTH es)`
      >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
          gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac result_array_length_state >>
          imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
          first_x_assum drule >> simp[type_check_def, assert_def, return_def] >>
          metis_tac[])
      >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
              ignore_bind_def, raise_def])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac pop_place_scopes_dom >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
      rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac lift_sum_state >> gvs[] >>
      first_x_assum drule >> simp[type_check_def, assert_def, return_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `LENGTH es = if has_gas then 3 else 2` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def] >>
      first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
      simp[type_check_def, assert_def, return_def] >> strip_tac >>
      rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule eval_send_preserves_non_accounts >> strip_tac >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
      gvs[] >> metis_tac[])
  >- suspend "IntCall"
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, push_log_def, option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
          raise_def, check_def, type_check_def, assert_def] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, get_accounts_def, option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[])
  >- suspend "CreateTarget"
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_exprs cx (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      gvs[] >> metis_tac[])
  >> rpt strip_tac >>
  qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_preserves_scopes_dom[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  res_tac >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  metis_tac[]
QED
(* Lock operations preserve scopes: needed for IntCall handler.
   Uses bind form (not ignore_bind) because earlier SIMP_TAC expands ignore_bind.
   Uses ≠ form because simp normalizes ¬(A ∨ B) to ¬A ∧ ¬B. *)
Theorem finally_intcall_handler_scopes[local]:
  ∀f nr mut cx prev s res s'.
    finally f
      (bind (set_scopes prev) (λx.
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ())) s = (res, s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
  \\ Cases_on `cx.nonreentrant_slot` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_scopes \\ gvs[]
QED

Theorem finally_set_scopes_scopes[local]:
  ∀f prev s res s'.
    finally f (set_scopes prev) s = (res,s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
QED

Theorem lock_acquire_cond_scopes_dom[local]:
  ∀nr slot_opt addr is_view st res st'.
    (if nr then
       case slot_opt of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) st = (res,st') ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_scopes \\ gvs[]
QED

Resume eval_mutual_preserves_scopes_dom[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3. _ ==>
       !st res st'. eval_exprs cx es st = (res,st') ==> _`
    (mp_tac o SRULE [type_check_def, assert_def, lift_option_type_def,
                     option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  disch_then assume_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rpt gen_tac >> rewrite_tac[Once evaluate_def] >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (drule type_check_scopes >> rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ r' = (res,st')` mp_tac >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  unabbrev_all_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  gvs[] >>
  BasicProvers.TOP_CASE_TAC >>
  first_x_assum drule >> strip_tac >>
  reverse (Cases_on `q`)
  >- (rw[] >> gvs[]) >>
  simp[bind_def, ignore_bind_def, get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> drule finally_set_scopes_scopes >> simp[] >>
      strip_tac >> gvs[]) >>
  strip_tac >>
  imp_res_tac finally_set_scopes_scopes >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[pop_function_def, push_function_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac lock_acquire_cond_scopes_dom >>
  imp_res_tac finally_intcall_handler_scopes >>
  gvs[]
QED

Finalise eval_mutual_preserves_scopes_dom

(* ========================================================================
   Main theorems (exported)
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

Theorem eval_base_place_preserves_scopes_dom:
  ∀cx bt st res st'. eval_base_place cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_base_place_preserves_var_in_scope:
  ∀cx st st' n bt res.
    eval_base_place cx bt st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_base_place_preserves_scopes_dom]
QED

Theorem eval_base_place_preserves_scopes_len:
  ∀bt cx st res st'.
    eval_base_place cx bt st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_base_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_exprs_preserves_scopes_dom:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
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

Theorem eval_target_place_preserves_scopes_dom:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_target_place_preserves_var_in_scope:
  !cx bt st res st' n. eval_target_place cx bt st = (res,st') ==>
    (var_in_scope st n <=> var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_target_place_preserves_scopes_dom]
QED

Theorem eval_target_place_preserves_scopes_len:
  !cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_target_place_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED
