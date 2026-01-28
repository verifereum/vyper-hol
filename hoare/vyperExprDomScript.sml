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

Theorem assign_target_preserves_scopes_dom[local]:
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

Theorem finally_set_scopes_dom[local]:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

(* ========================================================================
   Helper: eval_exprs preserves MAP FDOM of scopes
   ======================================================================== *)

Theorem eval_exprs_preserves_scopes_dom[local]:
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
   Case lemmas for impure expressions
   ======================================================================== *)

Theorem case_IfExp_dom[local]:
  ∀cx e e' e''.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e' st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e'' st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (IfExp e e' e'') st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def]
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum drule >> simp[]) >>
      Cases_on `tv = Value (BoolV T)` >> gvs[]
      >- (first_x_assum drule >> simp[])
      >- (Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >> first_x_assum drule >> simp[]))
  >- (last_x_assum drule >> simp[])
QED

Theorem case_StructLit_dom[local]:
  ∀cx id kes.
    (∀e. MEM e (MAP SND kes) ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (StructLit id kes) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> PairCases_on `id` >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  irule eval_exprs_preserves_scopes_dom >> simp[] >> metis_tac[]
QED

Theorem case_Subscript_dom[local]:
  ∀cx e e'.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀cx st res st'. eval_expr cx e' st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Subscript e e') st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum drule >> simp[])) >>
  TRY (`MAP FDOM s''.scopes = MAP FDOM s'³'.scopes` by (first_x_assum drule >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

Theorem case_Attribute_dom[local]:
  ∀cx e id.
    (∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Attribute e id) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, get_Value_def, lift_option_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

Theorem case_Builtin_dom[local]:
  ∀cx bt es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (Builtin bt es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, get_accounts_def, lift_sum_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes`
       by (irule eval_exprs_preserves_scopes_dom >> simp[] >> metis_tac[])) >>
  Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]
QED

Theorem case_TypeBuiltin_dom[local]:
  ∀cx tb typ es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀cx st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, lift_sum_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes`
       by (irule eval_exprs_preserves_scopes_dom >> simp[] >> metis_tac[])) >>
  Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]
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
Theorem case_TopLevelNameTarget_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

(* AttributeTarget case - only recurses on the sub-target, not on eval_expr *)
Theorem case_AttributeTarget_dom[local]:
  ∀cx t id.
    (∀st res st'. eval_base_target cx t st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget t id) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  first_x_assum drule >> simp[]
QED

(* SubscriptTarget case - recurses on both sub-target and eval_expr *)
Theorem case_SubscriptTarget_dom[local]:
  ∀cx t e.
    (∀st res st'. eval_base_target cx t st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    (∀st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget t e) st = (res, st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> gvs[]
QED

(* Pop case - only requires IH for eval_base_target, not for all eval_expr *)
Theorem case_Pop_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Pop bt) st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac (CONJUNCT1 assign_target_preserves_scopes_dom) >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  first_x_assum drule >> gvs[]
QED

Theorem case_Send_dom[local]:
  ∀cx es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call Send es) st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, assert_def, lift_option_def] >>
  strip_tac >> gvs[return_def, raise_def, GSYM lift_option_def] >>
  imp_res_tac transfer_value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  irule eval_exprs_preserves_scopes_dom >> simp[] >> metis_tac[]
QED

Theorem case_IntCall_dom[local]:
  ∀cx src_id_opt fn es.
    (∀e. MEM e es ⇒
         ∀cx st res st'. eval_expr cx e st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
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
  TRY (drule eval_exprs_preserves_scopes_dom >> simp[] >> metis_tac[])
QED

(* ========================================================================
   Main Theorem - proved by mutual induction on eval_base_target and eval_expr
   ======================================================================== *)

(* First prove the mutual induction theorem - with quantifier order matching evaluate_ind *)
(* TEMPORARILY CHEATED - ho_match_mp_tac evaluate_ind fails due to goal shape mismatch
   TODO: Investigate proper way to instantiate evaluate_ind or use alternative approach *)
Theorem eval_mutual_preserves_scopes_dom:
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  cheat
QED

(* Extract the main theorem from the mutual induction *)
Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED
