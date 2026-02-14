Theory vyperEvalExprPreservesScopesDom

Ancestors
  vyperInterpreter vyperLookup vyperScopePreservation

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
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def, get_Value_def] >>
  imp_res_tac get_Value_scopes >> gvs[]
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

(* ========================================================================
   Specialized evaluate_ind principle for scopes domain preservation

   We use evaluate_ind (which provides IHs for ALL recursive calls,
   including default argument evaluation in IntCall) instead of
   structural induction on expr (which cannot provide IHs for runtime
   expressions not in the syntax tree).

   Predicates:
   - P0-P4, P6 (statements, iterator, targets, for) = T (trivially true)
   - P5 (eval_base_target) = domain preservation
   - P7 (eval_expr) = domain preservation
   - P8 (eval_exprs) = domain preservation
   ======================================================================== *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\cx bt. !st res st'. eval_base_target cx bt st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p6 = ``\(cx:evaluation_context) (nm:num) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val scopes_dom_ind = save_thm("scopes_dom_ind", spec_ind_beta)
end

(* ========================================================================
   Helper lemmas for evaluate_ind cases (P5: eval_base_target)

   Statements match the evaluate_ind subgoal shapes exactly.
   ACCEPT_TAC works up to alpha-equivalence.
   ======================================================================== *)

(* Goal 1: NameTarget (no IH) *)
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
  >> Cases_on `exactly_one_option
                 (if IS_SOME (lookup_scopes (string_to_num nm) st.scopes) then
                    SOME (ScopedVar nm) else NONE) NONE` >> gvs[return_def, raise_def]
QED

(* Goal 2: TopLevelNameTarget (no IH) *)
Theorem case_TopLevelNameTarget_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def]
QED

(* Goal 3: AttributeTarget (unguarded IH for eval_base_target on t) *)
Theorem case_AttributeTarget_dom[local]:
  ∀cx t id.
    (∀st res st'. eval_base_target cx t st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget t id) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  first_x_assum drule >> simp[]
QED

(* Goal 4: SubscriptTarget (guarded IH for e, unguarded IH for t) *)
Theorem case_SubscriptTarget_dom[local]:
  ∀cx t e.
    (∀sa loc sbs sb.
       eval_base_target cx t sa = (INL (loc,sbs),sb) ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_base_target cx t st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget t e) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (
    qpat_x_assum `∀st res st'. eval_base_target _ _ _ = _ ⇒ _` drule >> simp[]) >>
  PairCases_on `x` >>
  qpat_x_assum `∀sa loc sbs sb. _` drule >> disch_then drule >> simp[]
QED

(* ========================================================================
   Helper lemmas for evaluate_ind cases (P7: eval_expr)
   ======================================================================== *)

(* Goal 5: Name (no IH) *)
Theorem case_Name_dom[local]:
  ∀cx id st res st'.
    eval_expr cx (Name id) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_scopes_id >> imp_res_tac get_immutables_scopes >>
  imp_res_tac lift_sum_scopes >> imp_res_tac return_scopes >> gvs[]
QED

(* Goal 6: TopLevelName (no IH) *)
Theorem case_TopLevelName_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_expr cx (TopLevelName (src_id_opt,id)) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_global_scopes >> gvs[]
QED

(* Goal 7: FlagMember (no IH) *)
Theorem case_FlagMember_dom[local]:
  ∀cx nsid mid st res st'.
    eval_expr cx (FlagMember nsid mid) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_flag_mem_scopes >> gvs[]
QED

(* Goal 8: IfExp (guarded IHs for e2,e3; unguarded for e1) *)
Theorem case_IfExp_dom[local]:
  ∀cx e1 e2 e3.
    (∀sa tv sb.
       eval_expr cx e1 sa = (INL tv,sb) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀sa tv sb.
       eval_expr cx e1 sa = (INL tv,sb) ⇒
       ∀st res st'. eval_expr cx e3 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (IfExp e1 e2 e3) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (IfExp _ _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def] >>
  strip_tac >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum drule >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >>
      last_x_assum (qspecl_then [`st`, `Value (BoolV T)`, `s''`] mp_tac) >>
      simp[] >> disch_then (qspecl_then [`s''`, `res`, `st'`] mp_tac) >> simp[] >>
      strip_tac >> first_x_assum drule >> simp[])
  >> IF_CASES_TAC >> gvs[raise_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`st`, `Value (BoolV F)`, `s''`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`s''`, `res`, `st'`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

(* Goal 9: Literal (no IH) *)
Theorem case_Literal_dom[local]:
  ∀cx l st res st'.
    eval_expr cx (Literal l) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, return_def]
QED

(* Goal 10: StructLit (unguarded IH for MAP SND kes) *)
Theorem case_StructLit_dom[local]:
  ∀cx src_id_opt id kes.
    (∀ks. ks = MAP FST kes ⇒
       ∀st res st'. eval_exprs cx (MAP SND kes) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (StructLit (src_id_opt,id) kes) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  first_x_assum (qspec_then `MAP FST kes` mp_tac) >> simp[] >>
  disch_then drule >> simp[]
QED

(* Goal 11: Subscript (guarded IH for e2, unguarded for e1) *)
Theorem case_Subscript_dom[local]:
  ∀cx e1 e2.
    (∀sa tv1 sb.
       eval_expr cx e1 sa = (INL tv1,sb) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Subscript e1 e2) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (Subscript _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >> gvs[] >>
  (* All 5 goals have e1 succeeded. Chain IHs for e1 and e2. *)
  first_x_assum $ drule_then assume_tac >>
  first_x_assum (qspecl_then [`st`, `tv1`, `s''`] mp_tac) >> simp[] >>
  disch_then $ drule_then assume_tac >> gvs[] >>
  (* Error goals closed; success path remains *)
  Cases_on `res'` >> gvs[return_def, bind_def, AllCaseEqs()] >>
  PairCases_on `y` >> gvs[bind_def, AllCaseEqs(), lift_option_def, return_def, raise_def] >>
  imp_res_tac read_storage_slot_scopes >> gvs[] >>
  Cases_on `evaluate_type (type_env ts) y2` >> gvs[return_def, raise_def]
QED

(* Goal 12: Attribute (unguarded IH) *)
Theorem case_Attribute_dom[local]:
  ∀cx e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Attribute e id) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, get_Value_def, lift_option_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

(* Goal 13: Builtin (guarded P8 IH) *)
Theorem case_Builtin_dom[local]:
  ∀cx bt es.
    (∀s'' x t.
       check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Builtin bt es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, get_accounts_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]) >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[check_def, assert_def, return_def] >>
  disch_then drule >> simp[]
QED

(* Goal 14: Pop (unguarded IH for eval_base_target) *)
Theorem case_Pop_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Pop bt) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac (CONJUNCT1 assign_target_preserves_scopes_dom) >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  first_x_assum drule >> gvs[]
QED

(* Goal 15: TypeBuiltin (guarded P8 IH) *)
Theorem case_TypeBuiltin_dom[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, assert_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]) >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[check_def, assert_def, return_def] >>
  disch_then drule >> simp[]
QED

(* Goal 16: Send (guarded P8 IH) *)
Theorem case_Send_dom[local]:
  ∀cx es v0.
    (∀s'' x t.
       check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call Send es v0) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, assert_def, lift_option_def] >>
  strip_tac >> gvs[return_def, raise_def, GSYM lift_option_def] >>
  imp_res_tac transfer_value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[check_def, assert_def, return_def] >>
  disch_then drule >> simp[]
QED

(* Goal 17: ExtCall (exact evaluate_ind shape) *)
Theorem case_ExtCall_dom[local]:
  ∀cx is_static func_name arg_types ret_type es drv.
    (∀s'' vs t s'³' x t' s'⁴' target_addr t'' s'⁵' value_opt arg_vals t'³'
         s'⁶' ts t'⁴' tenv s'⁷' calldata t'⁵' s'⁸' accounts t'⁶' s'⁹'
         tStorage t'⁷' txParams caller s'¹⁰' result t'⁸' success
         returnData accounts' tStorage' s'¹¹' x' t'⁹' s'¹²' x'' t'¹⁰'
         s'¹³' x'³' t'¹¹'.
       eval_exprs cx es s'' = (INL vs,t) ∧
       check (vs ≠ []) "ExtCall no target" s'³' = (INL x,t') ∧
       lift_option (dest_AddressV (HD vs)) "ExtCall target not address"
         s'⁴' = (INL target_addr,t'') ∧
       (if is_static then return (NONE,TL vs)
        else
          do
            check (TL vs ≠ []) "ExtCall no value";
            v <-
              lift_option (dest_NumV (HD (TL vs))) "ExtCall value not int";
            return (SOME v,TL (TL vs))
          od) s'⁵' = (INL (value_opt,arg_vals),t'³') ∧
       lift_option (get_self_code cx) "ExtCall get_self_code" s'⁶' =
       (INL ts,t'⁴') ∧ tenv = type_env ts ∧
       lift_option (build_ext_calldata tenv func_name arg_types arg_vals)
         "ExtCall build_calldata" s'⁷' = (INL calldata,t'⁵') ∧
       get_accounts s'⁸' = (INL accounts,t'⁶') ∧
       get_transient_storage s'⁹' = (INL tStorage,t'⁷') ∧
       txParams = vyper_to_tx_params cx.txn ∧ caller = cx.txn.target ∧
       lift_option
         (run_ext_call caller target_addr calldata value_opt accounts
            tStorage txParams) "ExtCall run failed" s'¹⁰' =
       (INL result,t'⁸') ∧
       (success,returnData,accounts',tStorage') = result ∧
       check success "ExtCall reverted" s'¹¹' = (INL x',t'⁹') ∧
       update_accounts (K accounts') s'¹²' = (INL x'',t'¹⁰') ∧
       update_transient (K tStorage') s'¹³' = (INL x'³',t'¹¹') ∧
       returnData = [] ∧ IS_SOME drv ⇒
       ∀st res st'.
         eval_expr cx (THE drv) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt gen_tac >> disch_then (fn conj2 =>
    let val (c1, c2) = CONJ_PAIR conj2
        val c1' = SIMP_RULE (srw_ss()) [check_def, lift_option_def, return_def, raise_def,
                      get_accounts_def, get_transient_storage_def, update_accounts_def,
                      update_transient_def, assert_def, bind_def, ignore_bind_def,
                      option_CASE_rator, COND_RATOR, pairTheory.UNCURRY,
                      AllCaseEqs(), PULL_EXISTS, pairTheory.PAIR_EQ] c1
    in
      assume_tac c1' >> assume_tac c2 >>
      rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, assert_def, lift_option_def, get_transient_storage_def,
           get_accounts_def, update_accounts_def, update_transient_def, lift_sum_def,
           COND_RATOR, pairTheory.UNCURRY, option_CASE_rator, CaseEq"option",
           sum_CASE_rator] >>
      strip_tac >> gvs[evaluation_state_accfupds] >>
      imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >>
      imp_res_tac get_accounts_scopes >> imp_res_tac get_transient_storage_scopes >>
      imp_res_tac update_accounts_scopes >> imp_res_tac update_transient_scopes >> gvs[] >>
      (* Close non-drv goals using eval_exprs IH *)
      TRY (qpat_x_assum `∀st res st'. eval_exprs _ _ _ = _ ⇒ _` drule >>
           simp[evaluation_state_accfupds] >> NO_TAC) >>
      (* Remaining: 2 drv goals (is_static=T and ¬is_static). Decompose result tuple. *)
      PairCases_on `result` >> gvs[] >>
      (* is_static=T: instantiate c1' with NONE for value_opt *)
      TRY (first_x_assum (qspecl_then [`st`, `vs`, `s''`, `target_addr`, `calldata`,
                                        `s''`, `s''`, `result2`, `result3`] mp_tac) >>
           simp[] >>
           disch_then drule >> simp[evaluation_state_accfupds] >>
           qpat_x_assum `∀st res st'. eval_exprs _ _ _ = _ ⇒ _` drule >> simp[] >>
           NO_TAC) >>
      (* ¬is_static: instantiate c1' with SOME v for value_opt *)
      first_x_assum (qspecl_then [`st`, `vs`, `s''`, `target_addr`, `ARB`,
                                   `SOME v'⁵'`, `TL (TL vs)`, `ARB`, `calldata`,
                                   `s''`, `s''`, `result2`, `result3`] mp_tac) >>
      simp[] >>
      disch_then drule >> simp[evaluation_state_accfupds] >>
      qpat_x_assum `∀st res st'. eval_exprs _ _ _ = _ ⇒ _` drule >> simp[]
    end)
QED

(* Goal 18: IntCall (exact evaluate_ind shape) *)
Theorem case_IntCall_dom[local]:
  ∀cx src_id_opt fn es v3.
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret
         body' s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs
         t'⁵' tenv all_mods all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰'
         rtv t'⁸' s'¹¹' cxf t'⁹'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
       sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
       check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
         "IntCall args length" s'⁵' = (INL x',t'³') ∧
       eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
       needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
       cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
       eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
       tenv = type_env ts ∧
       all_mods =
         (case ALOOKUP cx.sources cx.txn.target of NONE => [] | SOME m => m) ∧
       all_tenv = type_env_all_modules all_mods ∧
       lift_option (bind_arguments tenv args (vs ⧺ dflt_vs))
         "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
       get_scopes s'⁹' = (INL prev,t'⁷') ∧
       lift_option (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
         (INL rtv,t'⁸') ∧
       push_function (src_id_opt,fn) env cx s'¹¹' = (INL cxf,t'⁹') ⇒
       T) ∧
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret
         body' s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
       sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
       check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
         "IntCall args length" s'⁵' = (INL x',t'³') ∧
       eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
       needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
       cxd = cx with stk updated_by CONS (src_id_opt,fn) ⇒
       ∀st res st'.
         eval_exprs cxd needed_dflts st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup dflts sstup2 ret
         body' s'⁵' x' t'³'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ dflts = FST sstup ∧
       sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
       check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
         "IntCall args length" s'⁵' = (INL x',t'³') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call (IntCall (src_id_opt,fn)) es v3) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt gen_tac >> disch_then (fn conj3 =>
    let val (_, c23) = CONJ_PAIR conj3
        val (c2, c3) = CONJ_PAIR c23
        (* Simplify only decomposition equalities; preserve check/lift_option forms *)
        val c2' = SIMP_RULE (srw_ss()) [] c2
        val c3' = SIMP_RULE (srw_ss()) [] c3
    in
      rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      (* Don't expand check_def/lift_option_def so assumptions match IH guard forms *)
      simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           get_scopes_def, push_function_def, pop_function_def, set_scopes_def] >>
      strip_tac >>
      imp_res_tac lift_option_scopes >> imp_res_tac check_scopes >> gvs[] >>
      TRY (drule_all finally_set_scopes_dom >> strip_tac >> gvs[]) >>
      (* Apply IH for es (closes when es is the failing call) *)
      TRY (drule_all c3' >> simp[] >> NO_TAC) >>
      (* Chain: apply es IH, then dflts IH *)
      drule_all c3' >> strip_tac >>
      TRY (drule_all c2' >> simp[] >> NO_TAC) >>
      drule_all c2' >> strip_tac >> gvs[]
    end)
QED

(* ========================================================================
   Helper lemmas for evaluate_ind cases (P8: eval_exprs)
   ======================================================================== *)

(* Goal 19: eval_exprs [] (no IH) *)
Theorem case_eval_exprs_nil_dom[local]:
  ∀cx st res st'.
    eval_exprs cx [] st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

(* Goal 20: eval_exprs cons (exact evaluate_ind shape) *)
Theorem case_eval_exprs_cons_dom[local]:
  ∀cx e es.
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ get_Value tv s'³' = (INL v,t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  (* Cases where e fails: closed by unguarded IH *)
  TRY (qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` drule >> simp[] >> NO_TAC) >>
  (* Cases where e and get_Value both succeed: chain IHs *)
  qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` $ drule_then assume_tac >>
  metis_tac[]
QED

(* ========================================================================
   Main mutual theorem using evaluate_ind

   Each subgoal is closed by ACCEPT_TAC of the corresponding helper.
   ======================================================================== *)

Theorem eval_mutual_preserves_scopes_dom[local]:
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  MP_TAC scopes_dom_ind >> impl_tac >- (
    rpt conj_tac >>
    TRY (simp[] >> NO_TAC) >-
    ACCEPT_TAC case_NameTarget_dom >-
    ACCEPT_TAC case_TopLevelNameTarget_dom >-
    ACCEPT_TAC case_AttributeTarget_dom >-
    ACCEPT_TAC case_SubscriptTarget_dom >-
    ACCEPT_TAC case_Name_dom >-
    ACCEPT_TAC case_TopLevelName_dom >-
    ACCEPT_TAC case_FlagMember_dom >-
    ACCEPT_TAC case_IfExp_dom >-
    ACCEPT_TAC case_Literal_dom >-
    ACCEPT_TAC case_StructLit_dom >-
    ACCEPT_TAC case_Subscript_dom >-
    ACCEPT_TAC case_Attribute_dom >-
    ACCEPT_TAC case_Builtin_dom >-
    ACCEPT_TAC case_Pop_dom >-
    ACCEPT_TAC case_TypeBuiltin_dom >-
    ACCEPT_TAC case_Send_dom >-
    ACCEPT_TAC case_ExtCall_dom >-
    ACCEPT_TAC case_IntCall_dom >-
    ACCEPT_TAC case_eval_exprs_nil_dom >-
    ACCEPT_TAC case_eval_exprs_cons_dom
  ) >>
  simp[]
QED

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
