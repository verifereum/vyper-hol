Theory vyperScopePreservationLemmas

Ancestors
  vyperInterpreter vyperLookup

(* ===== Lemmas about scopes preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_scopes:
  !x st res st'. return x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[return_def]
QED

Theorem raise_scopes:
  !e st res st'. raise e st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[raise_def]
QED

Theorem get_scopes_scopes:
  ∀st res st'. get_scopes st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_scopes_def, return_def]
QED

Theorem check_scopes:
  !b s st res st'. check b s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[check_def, assert_def]
QED

Theorem lift_option_scopes:
  !x s st res st'. lift_option x s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_scopes:
  !x st res st'. lift_sum x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_scopes:
  !tv st res st'. get_Value tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_scopes_id:
  !st res st'. get_scopes st = (res, st') ==> st' = st
Proof
  rw[get_scopes_def, return_def]
QED

Theorem get_accounts_scopes:
  !st res st'. get_accounts st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_current_globals_scopes:
  !cx st res st'. get_current_globals cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem set_current_globals_scopes:
  !cx gbs st res st'. set_current_globals cx gbs st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_current_globals_def, return_def] >> simp[]
QED

Theorem get_immutables_scopes:
  !cx st res st'. get_immutables cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_immutables_def, get_immutables_module_def, bind_def, return_def, get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_scopes:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lookup_global_def, bind_def, return_def, get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def] >>
  Cases_on `FLOOKUP (get_module_globals src x).mutables n` >> fs[return_def, raise_def]
QED

Theorem set_global_scopes:
  !cx src n v st res st'. set_global cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_global_def, bind_def, return_def, get_current_globals_def, set_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem set_immutable_scopes:
  !cx src n v st res st'. set_immutable cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_immutable_def, bind_def, return_def, get_current_globals_def, set_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem push_log_scopes:
  !l st res st'. push_log l st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[push_log_def, return_def] >> simp[]
QED

Theorem transfer_value_scopes:
  !f t a st res st'. transfer_value f t a st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def, check_def, assert_def, update_accounts_def] >>
  gvs[raise_def] >> simp[]
QED

Theorem lookup_flag_mem_scopes:
  !cx nsid mid st res st'. lookup_flag_mem cx nsid mid st = (res, st') ==> st'.scopes = st.scopes
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

(* switch_BoolV preserves scopes if both branches preserve scopes. *)
Theorem switch_BoolV_scopes:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ⇒
    st'.scopes = st.scopes
Proof
  rw[switch_BoolV_def, raise_def]
QED

(* finally with pop_function restores scopes to prev. *)
Theorem finally_pop_function_scopes:
  ∀f prev st res st'.
    finally f (pop_function prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[pop_function_def, finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

(* Helper: finally with set_scopes restores scopes to the given value.
   Same as finally_pop_function_scopes but uses set_scopes directly. *)
Theorem finally_set_scopes:
  ∀f prev st res st'.
    finally f (set_scopes prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem find_containing_scope_map_fdom:
  ∀id sc pre env v rest a'.
    find_containing_scope id sc = SOME (pre, env, v, rest) ⇒
    MAP FDOM (pre ++ env |+ (id, a') :: rest) = MAP FDOM sc
Proof
  rpt strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  gvs[] >>
  `id IN FDOM env` by gvs[finite_mapTheory.FLOOKUP_DEF] >>
  gvs[pred_setTheory.ABSORPTION_RWT]
QED

Theorem assign_target_preserves_scopes_dom:
  (∀cx gv ao st res st'. assign_target cx gv ao st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes) ∧
  (∀cx gvs vs st res st'. assign_targets cx gvs vs st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes)
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar case *)
  >- (strip_tac >> gvs[assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
      Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
      PairCases_on `x` >> gvs[bind_def, lift_sum_def] >>
      Cases_on `assign_subscripts x2 (REVERSE is) ao` >>
      gvs[return_def, raise_def, bind_def, ignore_bind_def, set_scopes_def] >>
      drule find_containing_scope_map_fdom >> simp[])
  (* TopLevelVar case *)
  >- (strip_tac >> gvs[assign_target_def, bind_def] >>
      Cases_on `lookup_global cx src_id_opt (string_to_num id) st` >> gvs[] >>
      drule lookup_global_scopes >> strip_tac >>
      Cases_on `q` >> gvs[] >>
      gvs[lift_option_def, AllCaseEqs(), return_def, raise_def]
      >- (imp_res_tac lift_sum_scopes >> gvs[] >>
          gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def]
          >- (imp_res_tac set_global_scopes >> gvs[] >>
              Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def])
          >- (imp_res_tac set_global_scopes >> gvs[] >>
              Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]))
      >- (imp_res_tac lift_sum_scopes >> Cases_on `get_module_code cx src_id_opt` >>
          gvs[return_def, raise_def])
      >- (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]))
  (* ImmutableVar case *)
  >- (strip_tac >> gvs[assign_target_def, bind_def] >>
      Cases_on `get_immutables cx st` >> gvs[] >>
      drule get_immutables_scopes >> strip_tac >>
      Cases_on `q` >> gvs[] >>
      gvs[lift_option_def, AllCaseEqs(), return_def, raise_def]
      >- (imp_res_tac lift_sum_scopes >> gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def]
          >- (imp_res_tac set_immutable_scopes >> gvs[] >>
              Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def])
          >- (imp_res_tac set_immutable_scopes >> gvs[] >>
              Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def]))
      >- (imp_res_tac lift_sum_scopes >> gvs[] >>
          Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def])
      >- (Cases_on `FLOOKUP x (string_to_num id)` >> gvs[return_def, raise_def]))
  (* TupleTargetV with TupleV - uses IH *)
  >- (rpt strip_tac >>
      gvs[assign_target_def, bind_def, check_def, assert_def, return_def, raise_def,
          ignore_bind_def, AllCaseEqs()])
  (* TupleTargetV error cases - all just raise *)
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
  (* assign_targets [] [] *)
  >- simp[assign_target_def, return_def]
  (* assign_targets cons case - uses IH *)
  >- (rpt strip_tac >>
      gvs[assign_target_def, bind_def, AllCaseEqs(), return_def, get_Value_def] >>
      res_tac >> imp_res_tac get_Value_scopes >> gvs[] >> TRY (first_x_assum drule >> simp[]))
  (* assign_targets length mismatch cases *)
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
QED

Theorem finally_set_scopes_dom:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem eval_exprs_preserves_scopes_dom:
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
