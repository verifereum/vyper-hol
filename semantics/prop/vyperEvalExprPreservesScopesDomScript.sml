Theory vyperEvalExprPreservesScopesDom
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperCreate vyperCreateFrame vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperAbiFrame vyperCallOutcome[ignore_grammar]

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

(* Legacy target induction, superseded by the place induction below.
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
   - P9/P10 (delayed ABI expression/list) = domain preservation
   ======================================================================== *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\cx bt. !st res st'. eval_base_target cx bt st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p6 = ``\(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p9 = ``\cx e. !st res st'. eval_abi_expr cx e st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p10 = ``\cx es. !st res st'. eval_abi_exprs cx es st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10] evaluate_ind
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
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  rpt strip_tac >>
  Cases_on `IS_SOME (lookup_scopes nm st.scopes)` >> gvs[return_def, raise_def]
QED

(* Goal 2: TopLevelNameTarget (no IH) *)
Theorem case_TopLevelNameTarget_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `get_module_code cx src_id_opt` >> simp[return_def, raise_def] >>
  Cases_on `is_immutable_decl id x` >> simp[return_def]
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
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY]
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
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac lift_option_type_scopes >> gvs[] >>
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
  ∀cx ty id st res st'.
    eval_expr cx (Name ty id) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >>
  Cases_on `lookup_scopes_val id st.scopes` >> gvs[return_def, raise_def]
QED

(* Goal 6: TopLevelName (no IH) *)
Theorem case_TopLevelName_dom[local]:
  ∀cx ty src_id_opt id st res st'.
    eval_expr cx (TopLevelName ty (src_id_opt,id)) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_global_scopes >> gvs[]
QED

(* Goal 7: FlagMember (no IH) *)
Theorem case_FlagMember_dom[local]:
  ∀cx ty nsid mid st res st'.
    eval_expr cx (FlagMember ty nsid mid) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_flag_mem_scopes >> gvs[]
QED

(* Goal 8: IfExp (guarded IHs for e2,e3; unguarded for e1) *)
Theorem case_IfExp_dom[local]:
  ∀cx ty e1 e2 e3.
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
      eval_expr cx (IfExp ty e1 e2 e3) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (IfExp _ _ _ _) _ = _` mp_tac >>
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
  ∀cx ty l st res st'.
    eval_expr cx (Literal ty l) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, return_def]
QED

(* Goal 10: StructLit (unguarded IH for MAP SND kes) *)
Theorem case_StructLit_dom[local]:
  ∀cx ty src_id_opt id kes.
    (∀ks. ks = MAP FST kes ⇒
       ∀st res st'. eval_exprs cx (MAP SND kes) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (StructLit ty (src_id_opt,id) kes) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def]
QED

(* Goal 11: Subscript (guarded IH for e2, unguarded for e1) *)
Theorem case_Subscript_dom[local]:
  ∀cx ty e1 e2.
    (∀sa tv1 sb.
       eval_expr cx e1 sa = (INL tv1,sb) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Subscript ty e1 e2) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac check_array_bounds_state >> gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  first_x_assum (qspecl_then [`st`, `tv1`, `s''`] mp_tac) >> simp[] >>
  disch_then $ drule_then assume_tac >> gvs[] >>
  rename1 `lift_sum _ _ = (INL subscript_res, _)` >>
  Cases_on `subscript_res` >> gvs[return_def, bind_def, AllCaseEqs()] >>
  PairCases_on `y` >> gvs[bind_def, AllCaseEqs(), lift_option_def, lift_option_type_def, return_def, raise_def] >>
  imp_res_tac read_storage_slot_scopes >> gvs[]
QED

(* Goal 12: Attribute (unguarded IH) *)
Theorem case_Attribute_dom[local]:
  ∀cx ty e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Attribute ty e id) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, get_Value_def, lift_option_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >> gvs[]
QED

*)
(* Pure builtin tails need only the state projection, not their result cases. *)
Theorem builtin_dom_frames[local]:
  state_rel_frame (λs t. MAP FDOM s.scopes = MAP FDOM t.scopes) (lift_sum rs) ∧
  state_rel_frame (λs t. MAP FDOM s.scopes = MAP FDOM t.scopes)
    (result_array_length cx tv) ∧
  state_rel_frame (λs t. MAP FDOM s.scopes = MAP FDOM t.scopes) (read_result cx top)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  FIRST [drule lift_sum_state, drule result_array_length_state,
    drule read_result_state] >> simp[]
QED

Theorem assign_dom_frame[local]:
  state_rel_frame (λs t. MAP FDOM s.scopes = MAP FDOM t.scopes)
    (pop_place cx target)
Proof
  simp[state_rel_frame_result] >>
  metis_tac[pop_place_scopes_dom]
QED

local
  val relation = ``λ(s:evaluation_state) t. MAP FDOM s.scopes = MAP FDOM t.scopes``;
  fun specialise th =
    ISPEC relation (GEN (first (fn v => fst (dest_var v) = "R")
      (free_vars (concl th))) th) |> SRULE [];
  val result = specialise state_rel_frame_result;
  val bind = specialise state_rel_frame_bind_guarded;
  val finally = specialise state_rel_frame_finally;
  val abi = CONJUNCTS (specialise state_rel_frame_abi_primitives);
  val abi_place = specialise state_rel_frame_abi_place;
  val assign = assign_dom_frame;
  val leaves = List.foldl (fn (th,net) =>
      Net.insert (concl th, MATCH_ACCEPT_TAC th) net) Net.empty
    (CONJUNCTS (specialise state_rel_frame_locals_primitives) @
     CONJUNCTS builtin_dom_frames @ abi @ [assign, abi_place]);
  fun leaf (asl,w) = FIRST (Net.match w leaves) (asl,w);
  (* Discharge only the actual success guard; never simplify an IH. *)
  fun ih (asl,w) =
    if not (is_comb w andalso
      List.exists (fn name =>
        total (fst o dest_const o fst o strip_comb o rand) w = SOME name)
        ["eval_expr", "eval_exprs", "eval_base_place", "eval_target_place", "eval_abi_expr", "eval_abi_exprs"]) then NO_TAC (asl,w)
    else let
      val normalise = SIMP_RULE bool_ss [oneTheory.one, ignore_bind_def];
      val facts = List.concat (map (CONJUNCTS o normalise o ASSUME) asl);
      fun discharge th =
        if is_imp (snd (strip_forall (concl th))) then
          discharge (tryfind (MATCH_MP th) facts)
        else th;
    in
      FIRST (map (fn th => fn g => ACCEPT_TAC (discharge
        (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] th)) g) facts) (asl,w)
    end;
in
  val BUILTIN_DOM_TAC =
    rpt (fn g as (_,w) =>
      if is_forall w andalso type_of (#1 (dest_forall w)) <> ``:evaluation_state``
      then gen_tac g else NO_TAC g) >>
    (fn g as (_,w) => if is_imp w then strip_tac g else ALL_TAC g) >>
    CONV_TAC (REWR_CONV (GSYM result)) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM result]) >>
    rpt (FIRST [leaf, ih,
      MATCH_MP_TAC bind >> conj_tac,
      MATCH_MP_TAC finally >> conj_tac,
      CONV_TAC (RAND_CONV BETA_CONV),
      CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
      CHANGED_TAC (simp_tac bool_ss [pairTheory.UNCURRY, pairTheory.pair_case_thm]),
      CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
      gen_tac, strip_tac,
      CHANGED_TAC (fn (asl,w) => simp_tac (srw_ss())
        (map ASSUME (List.filter (not o is_forall) asl)) (asl,w)),
      BasicProvers.PURE_CASE_TAC]);
end;

(* Legacy constructor lemmas, replaced by the canonical place induction.
(* Goal 13: Builtin (guarded P8 IH) *)
Theorem case_Builtin_dom[local]:
  ∀cx ty bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ∧
       bt ≠ Len ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ∧
       bt = Len ⇒
       ∀st res st'. eval_expr cx (HD es) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Builtin ty bt es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  BUILTIN_DOM_TAC
QED

(* Goal 14: Pop (unguarded IH for eval_base_target) *)
Theorem case_Pop_dom[local]:
  ∀cx ty bt.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Pop ty bt) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac (CONJUNCT1 assign_target_preserves_scopes_dom) >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >> imp_res_tac lift_option_type_scopes >> gvs[]
QED

(* TypeBuiltin is proved in the mutual induction with separate guarded IHs
   for AbiEncode's eval_abi_exprs and the eager branch's eval_exprs. *)

*)
(* Domain preservation follows the evaluator's mutual induction.
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

(* Legacy target-only mutual statement and dispatch:
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_abi_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx es st res st'. eval_abi_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes)
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
    suspend "TypeBuiltin" >-
    ACCEPT_TAC case_Send_dom >-
    ACCEPT_TAC case_ExtCall_dom >-
    suspend "IntCall" >-
    ACCEPT_TAC case_RawCallTarget_dom >-
    ACCEPT_TAC case_RawCallCalldataTarget_dom >-
    ACCEPT_TAC case_RawLog_dom >-
    ACCEPT_TAC case_RawRevert_dom >-
    ACCEPT_TAC case_SelfDestructTarget_dom >-
    suspend "CreateTarget" >-
    ACCEPT_TAC case_eval_exprs_nil_dom >-
    ACCEPT_TAC case_eval_exprs_cons_dom >>
    BUILTIN_DOM_TAC
  ) >>
  simp[]
*)
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
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx e st res st'. eval_abi_expr cx e st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes) /\
  (!cx es st res st'. eval_abi_exprs cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes)
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
  >- suspend "TypeBuiltin"
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
      imp_res_tac read_results_state >>
      gvs[] >>
      rpt (qpat_x_assum `∀a b c d e f. _` drule_all >> strip_tac) >>
      rpt (qpat_x_assum `∀a b c. _` drule_all >> strip_tac) >>
      metis_tac[])
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
  >- (rpt strip_tac >>
  qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[])
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr_results cx (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> metis_tac[]) >>
  BUILTIN_DOM_TAC
QED

Resume eval_mutual_preserves_scopes_dom[TypeBuiltin]:
  rpt gen_tac >> strip_tac >> Cases_on `tb` >> gvs[] >> BUILTIN_DOM_TAC
QED

Resume eval_mutual_preserves_scopes_dom[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
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
       !st res st'. eval_expr_results cx es st = (res,st') ==> _`
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
  imp_res_tac read_results_state >>
  imp_res_tac lock_acquire_cond_scopes_dom >>
  imp_res_tac finally_intcall_handler_scopes >>
  gvs[]
QED

Finalise eval_mutual_preserves_scopes_dom

(* ========================================================================
   Main theorems (exported)
   ======================================================================== *)

Theorem eval_abi_expr_preserves_scopes_dom:
  eval_abi_expr cx e st = (res,rt) ==> MAP FDOM st.scopes = MAP FDOM rt.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_abi_exprs_preserves_scopes_dom:
  eval_abi_exprs cx es st = (res,rt) ==> MAP FDOM st.scopes = MAP FDOM rt.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

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

Theorem eval_expr_results_preserves_scopes_dom:
  eval_expr_results cx es st = (res,st') ==>
    MAP FDOM st.scopes = MAP FDOM st'.scopes
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
