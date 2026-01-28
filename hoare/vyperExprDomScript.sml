Theory vyperExprDom

(* Theorems about expression evaluation.
 *)

Ancestors
  vyperInterpreter vyperScopes vyperLookup vyperExpr

(* ========================================================================
   Helper: find_containing_scope preserves MAP FDOM
   ======================================================================== *)

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

(* ========================================================================
   Helper: assign_target preserves MAP FDOM of scopes
   ======================================================================== *)

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

(* ========================================================================
   Helper: finally with set_scopes restores scopes to the given value
   ======================================================================== *)

Theorem finally_set_scopes_dom:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

(* ========================================================================
   Helper: eval_exprs preserves MAP FDOM of scopes
   ======================================================================== *)

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

(* ========================================================================
   Helper lemmas for individual eval_base_target cases (for mutual induction)
   ======================================================================== *)

(* NameTarget case - does not call eval_expr *)
Theorem case_NameTarget_dom:
  ∀cx nm st res st'.
    eval_base_target cx (NameTarget nm) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
      get_scopes_def, get_immutables_def, get_immutables_module_def,
      get_current_globals_def, lift_option_def, lift_sum_def] >>
  TRY (rename1 `_ = (INL ivo, s_ivo)` >>
       Cases_on `exactly_one_option
                   (if IS_SOME (lookup_scopes (string_to_num nm) st.scopes) then
                      SOME (ScopedVar nm) else NONE) ivo` >> gvs[return_def, raise_def]) >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def, bind_def, get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]
QED

(* TopLevelNameTarget case - does not call eval_expr *)
Theorem case_TopLevelNameTarget_dom:
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
Theorem case_IfExp_ind:
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
Theorem case_Subscript_ind:
  ∀e e0.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e0 st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Subscript e e0) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum (qspec_then `cx` drule) >> simp[])) >>
  TRY (first_x_assum (qspec_then `cx` drule) >> simp[] >> strip_tac) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

(* Attribute: P0 e ⇒ ∀s. P0 (Attribute e s) *)
Theorem case_Attribute_ind:
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
Theorem case_SubscriptTarget_ind:
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
Theorem case_AttributeTarget_ind:
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
Theorem case_Pop_ind:
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
Theorem case_StructLit_ind:
  ∀kes.
    (∀e. MEM e (MAP SND kes) ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀src_id_opt id cx st res st'.
      eval_expr cx (StructLit (src_id_opt, id) kes) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  drule_all eval_exprs_preserves_scopes_dom >> simp[]
QED

(* Builtin: P4 l ⇒ ∀b. P0 (Builtin b l) *)
Theorem case_Builtin_ind:
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
      drule_all eval_exprs_preserves_scopes_dom >> simp[])
  >- (drule_all eval_exprs_preserves_scopes_dom >> simp[] >>
      Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def])
  >- (drule_all eval_exprs_preserves_scopes_dom >> simp[])
QED

(* TypeBuiltin: P4 l ⇒ ∀t t0. P0 (TypeBuiltin t0 t l) *)
Theorem case_TypeBuiltin_ind:
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
  drule_all eval_exprs_preserves_scopes_dom >> simp[]
QED

(* Call: P4 l ⇒ ∀c. P0 (Call c l)
   Need to case split on c (Send, ExtCall, StaticCall, IntCall) *)
Theorem case_Call_Send_ind:
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
  drule_all eval_exprs_preserves_scopes_dom >> simp[]
QED

Theorem case_Call_IntCall_ind:
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
  TRY (drule_all eval_exprs_preserves_scopes_dom >> simp[])
QED

(* ========================================================================
   Main Theorem - proved by structural induction on expr/base_target types
   ======================================================================== *)

(* Predicates for structural induction *)
Definition scopes_P0_def:
  scopes_P0 e = ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
End

Definition scopes_P1_def:
  scopes_P1 bt = ∀cx st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
End

Definition scopes_P2_def:
  scopes_P2 kes = ∀e. MEM e (MAP SND kes) ⇒ scopes_P0 e
End

Definition scopes_P3_def:
  scopes_P3 ke = scopes_P0 (SND ke)
End

Definition scopes_P4_def:
  scopes_P4 es = ∀e. MEM e es ⇒ scopes_P0 e
End

Theorem eval_mutual_preserves_scopes_dom:
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
          gvs[evaluate_def, bind_def, AllCaseEqs()] >>
          imp_res_tac get_current_globals_scopes >> imp_res_tac lift_option_scopes >>
          imp_res_tac lift_sum_scopes >> imp_res_tac return_scopes >> gvs[] >>
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
          >- gvs[evaluate_def, raise_def]
          >- gvs[evaluate_def, raise_def]
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

(* Extract the main theorem from the mutual induction *)
Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED
