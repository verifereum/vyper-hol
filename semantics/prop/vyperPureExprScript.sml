Theory vyperPureExpr
Ancestors
  vyperMisc vyperContext vyperState vyperStorageBackend vyperInterpreter vyperLookup vyperStatePreservation
  vyperPlaceFrames vyperAbiOperand vyperAbiFrame vyperAbiReadOnly vyperAbiAppendFrame vyperCallOutcomeFrame

(* Pure expressions: expressions that do not modify state. *)
Definition pure_expr_def:
  pure_expr (Name _ _) = T ∧
  pure_expr (TopLevelName _ _) = T ∧
  pure_expr (FlagMember _ _ _) = T ∧
  pure_expr (Literal _ _) = T ∧
  pure_expr (IfExp _ e1 e2 e3) = (pure_expr e1 ∧ pure_expr e2 ∧ pure_expr e3) ∧
  pure_expr (StructLit _ _ kes) = EVERY pure_expr (MAP SND kes) ∧
  pure_expr (Subscript _ e1 e2) = (pure_expr e1 ∧ pure_expr e2) ∧
  pure_expr (Attribute _ e _) = pure_expr e ∧
  pure_expr (Builtin _ _ es) = EVERY pure_expr es ∧
  pure_expr (TypeBuiltin _ _ _ es) = EVERY pure_expr es ∧
  pure_expr _ = F
Termination
  WF_REL_TAC `measure expr_size` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

(* Specialize the canonical evaluator induction theorem. Only expression
   and expression-list evaluation carry whole-state preservation obligations. *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T``
  val p4 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> pure_expr e ==> st = st'``
  val p5 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY pure_expr es ==> st = st'``
  val p6 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p7 = p6
  val p8 = ``\(cx:evaluation_context) (g:assignment_target) (v:value). T``
  val p9 = ``\(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T``
  val p10 = ``\(cx:evaluation_context) (es:expr list). T``
  val p11 = ``\cx e. !st res st'. eval_abi_expr cx e st = (res,st') ==> pure_expr e ==> abi_append st st'``
  val p12 = ``\cx es. !st res st'. eval_abi_exprs cx es st = (res,st') ==> EVERY pure_expr es ==> abi_append st st'``
in
  val expr_state_ind_principle =
    CONV_RULE (DEPTH_CONV BETA_CONV)
      (SPECL [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12] evaluate_ind)
end

Theorem canonical_observations_state[local]:
  (read_result cx r st = (v,st') ==> st' = st) /\
  (select_result cx ty r sb st = (w,st') ==> st' = st) /\
  (conditional_result cx r st = (x,st') ==> st' = st) /\
  (result_array_length cx r st = (n,st') ==> st' = st)
Proof
  metis_tac[read_result_state, select_result_state,
            conditional_result_state, result_array_length_state]
QED

(* ------------------------------------------------------------------------
   Individual Case Lemmas
   ------------------------------------------------------------------------ *)

Theorem case_Name[local]:
  ∀cx ty id.
    (∀st res st'.
       eval_expr cx (Name ty id) st = (res, st') ⇒
       st = st')
Proof
  simp[evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def] >>
  rpt strip_tac >>
  Cases_on `IS_SOME (lookup_scopes id st.scopes)` >>
  gvs[return_def, raise_def]
QED

Theorem case_TopLevelName[local]:
  ∀cx ty src_id_opt id.
    (∀st res st'.
       eval_expr cx (TopLevelName ty (src_id_opt, id)) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_global_state >> simp[]
QED

Theorem case_FlagMember[local]:
  ∀cx ty nsid mid.
    (∀st res st'.
       eval_expr cx (FlagMember ty nsid mid) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_flag_mem_state >> simp[]
QED

Theorem case_IfExp[local]:
  ∀cx ty e1 e2 e3.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st = st') ∧
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e3 st = (res, st') ⇒ pure_expr e3 ⇒ st = st') ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (IfExp ty e1 e2 e3) st = (res, st') ⇒
       pure_expr (IfExp ty e1 e2 e3) ⇒ st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def,
      pure_expr_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >> metis_tac[]
QED

Theorem case_Literal[local]:
  ∀cx ty l.
    (∀st res st'.
       eval_expr cx (Literal ty l) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def, return_def]
QED

(* Case: StructLit - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates MAP SND kes as expressions, then constructs struct.
   If eval_exprs preserves the whole state (IH), so does the result.

   Plan reference: Case 6 *)
Theorem case_StructLit[local]:
  ∀cx ty src kes.
    (∀st res st'.
       eval_exprs cx (MAP SND kes) st = (res, st') ⇒
       EVERY pure_expr (MAP SND kes) ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (StructLit ty src kes) st = (res, st') ⇒
       pure_expr (StructLit ty src kes) ⇒ st = st')
Proof
  rpt strip_tac >> PairCases_on `src` >>
  fs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, return_def] >> gvs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> gvs[listTheory.EVERY_MAP]
QED

Theorem case_Subscript[local]:
  ∀cx ty e1 e2.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st = st') ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (Subscript ty e1 e2) st = (res, st') ⇒
       pure_expr (Subscript ty e1 e2) ⇒ st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Theorem case_Attribute[local]:
  ∀cx ty e id.
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (Attribute ty e id) st = (res, st') ⇒
       pure_expr (Attribute ty e id) ⇒ st = st')
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Theorem case_Builtin[local]:
  ∀cx ty bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x, t) ∧
       bt ≠ Len ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x, t) ∧
       bt = Len ⇒
       ∀st res st'.
         eval_expr cx (HD es) st = (res, st') ⇒ pure_expr (HD es) ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (Builtin ty bt es) st = (res, st') ⇒
       pure_expr (Builtin ty bt es) ⇒ st = st')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Len`
  >- (rpt strip_tac >>
      gvs[evaluate_def, pure_expr_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >> gvs[] >>
      `pure_expr (HD es)` by
        (Cases_on `es` >> gvs[builtin_args_length_ok_def]) >>
      metis_tac[type_check_def, assert_def, return_def]) >>
  rpt strip_tac >>
  gvs[evaluate_def, pure_expr_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def,
      get_accounts_def, lift_sum_def, AllCaseEqs()] >>
  gvs[get_accounts_def, ETA_THM, return_def, raise_def,
      sum_CASE_rator, AllCaseEqs()] >> metis_tac[]
QED

Theorem case_Pop[local]:
  ∀cx ty bt.
    (∀st res st'.
       eval_expr cx (Pop ty bt) st = (res, st') ⇒
       pure_expr (Pop ty bt) ⇒ st = st')
Proof
  rw[pure_expr_def]
QED

(* Obsolete eager-only helper retained. The mutual TypeBuiltin proof below
   now uses allocation-only framing for delayed ABI operands.
Theorem case_TypeBuiltin[local]:
  ∀cx ty tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (TypeBuiltin ty tb typ es) st = (res, st') ⇒
       pure_expr (TypeBuiltin ty tb typ es) ⇒ st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >>
  metis_tac[]
QED

*)

(* All Call cases are vacuously true since pure_expr (Call _ _ _) = F *)
Theorem case_Call[local]:
  ∀cx ty c es drv st res st'.
    eval_expr cx (Call ty c es drv) st = (res, st') ⇒
    pure_expr (Call ty c es drv) ⇒ st = st'
Proof
  rw[pure_expr_def]
QED

Theorem case_eval_exprs_nil[local]:
  ∀cx.
    (∀st res st'.
       eval_exprs cx [] st = (res, st') ⇒
       st = st')
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv, t) ∧ read_result cx tv s'3' = (INL v, t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ∧
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ⇒
    (∀st res st'.
       eval_exprs cx (e::es) st = (res, st') ⇒
       EVERY pure_expr (e::es) ⇒ st = st')
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Main Mutual Induction Theorem

   Assembles individual case lemmas into the full mutual induction.
   Ordinary pure expressions preserve the complete state. Delayed pure ABI
   operands may append local/immutable captures, but preserve all existing cells
   and all other fields. The outer AbiEncode releases both suffixes on errors too.

   We use a specialized version of evaluate_ind with:
   - P0-P3 and P6-P10 (statements/places/tuple assignment/results) = T
   - P4/P5 = complete state preservation under purity
   - P11/P12 = allocation-only ABI framing under purity
   ------------------------------------------------------------------------ *)

(* Derive specialized induction principle for expr_state_mutual.
   This encapsulates the SML needed to specialize evaluate_ind. *)
(* Historical pre-place specialization (superseded above).
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p6 = ``\(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> pure_expr e ==> st = st'``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY pure_expr es ==> st = st'``
  val p9 = ``\cx e. !st res st'. eval_abi_expr cx e st = (res,st') ==> pure_expr e ==> abi_append st st'``
  val p10 = ``\cx es. !st res st'. eval_abi_exprs cx es st = (res,st') ==> EVERY pure_expr es ==> abi_append st st'``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val expr_state_ind_principle = save_thm("expr_state_ind_principle", spec_ind_beta)
end
*)
(* The canonical place specialization assigns whole-state preservation
   to P4 (eval_expr) and P5 (eval_exprs), and T to every other predicate.
   Dispatch examines only the conclusion spine, never the guarded IHs.
   ------------------------------------------------------------------------ *)

(* expr_state_ind_principle is specialized above the constructor lemmas. *)

(* Main mutual induction. *)
Theorem expr_state_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ∧
  (∀cx e st res st'. eval_abi_expr cx e st = (res,st') ⇒ pure_expr e ⇒ abi_append st st') ∧
  (∀cx es st res st'. eval_abi_exprs cx es st = (res,st') ⇒ EVERY pure_expr es ⇒ abi_append st st')
Proof
  MP_TAC expr_state_ind_principle >> impl_tac >- (
    rpt conj_tac >>
    (* Do not simplify purity inside the guarded IHs: internal calls have
       large default-argument guards. Unfold only the conclusion's purity
       assumption, once, and leave the case-lemma IHs unchanged. *)
    TRY (rpt (gen_tac ORELSE disch_tac) >> ACCEPT_TAC TRUTH) >>
    TRY (rpt strip_tac >>
         qpat_x_assum `pure_expr _` mp_tac >>
         CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [pure_expr_def])) >>
         simp_tac bool_ss [] >> NO_TAC) >-
    metis_tac[case_Name] >-
    metis_tac[case_TopLevelName] >-
    metis_tac[case_FlagMember] >-
    ACCEPT_TAC case_IfExp >-
    metis_tac[case_Literal] >-
    metis_tac[case_StructLit] >-
    ACCEPT_TAC case_Subscript >-
    ACCEPT_TAC case_Attribute >-
    ACCEPT_TAC case_Builtin >-
    suspend "TypeBuiltin" >-
    metis_tac[case_eval_exprs_nil] >-
    ACCEPT_TAC case_eval_exprs_cons >>
    rpt strip_tac >>
    FIRST [qpat_x_assum `eval_abi_expr _ _ _ = _` mp_tac,
           qpat_x_assum `eval_abi_exprs _ _ _ = _` mp_tac] >>
    simp[Once evaluate_def, bind_def, ignore_bind_def,
      return_def, raise_def, AllCaseEqs(), switch_BoolV_def] >>
    rpt strip_tac >> gvs[pure_expr_def] >>
    imp_res_tac abi_readonly_states >>
    imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >> gvs[] >>
    TRY (FIRST [drule (lookup_abi_local_append |> SRULE [state_rel_frame_result]),
      drule (lookup_abi_global_append |> SRULE [state_rel_frame_result])] >>
      simp[] >> NO_TAC) >>
    res_tac >> gvs[] >>
    TRY (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
      rpt IF_CASES_TAC >> simp[raise_def] >> strip_tac >> gvs[]) >>
    res_tac >> gvs[] >>
    TRY (irule abi_append_trans >> first_assum (irule_at Any) >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `∀st res rt. eval_abi_expr _ _ st = (res,rt) ⇒ _` drule >>
    strip_tac >> drule_all abi_append_trans >> simp[]
  ) >>
  simp[]
(* Incoming eager-only dispatcher, superseded by ABI-aware induction above.
  let
    fun spine tm ants =
      if is_forall tm then spine (snd (dest_forall tm)) ants
      else if is_imp tm then
        let val (a,b) = dest_imp tm in spine b (a::ants) end
      else (tm, ants)
    fun head_name tm =
      let val h = fst (strip_comb tm)
      in if is_const h then fst (dest_const h) else "" end
    fun introduce (g as (_,w)) =
      if is_forall w then (gen_tac >> introduce) g
      else if is_imp w then (disch_tac >> introduce) g
      else all_tac g
    fun dispatch (g as (_,w)) =
      let
        val (concl, ants) = spine w []
        val purity = List.find
          (fn a => head_name a = "pure_expr" orelse head_name a = "EVERY") ants
      in
        if aconv concl T then
          introduce >> ACCEPT_TAC TRUTH
        else case purity of
          NONE => FAIL_TAC "missing outer purity premise"
        | SOME p =>
          if head_name p = "EVERY" then
            if listSyntax.is_nil (last (snd (strip_comb p))) then
              metis_tac[case_eval_exprs_nil]
            else ACCEPT_TAC case_eval_exprs_cons
          else
            case head_name (rand p) of
              "Name" => metis_tac[case_Name]
            | "TopLevelName" => metis_tac[case_TopLevelName]
            | "FlagMember" => metis_tac[case_FlagMember]
            | "IfExp" => ACCEPT_TAC case_IfExp
            | "Literal" => metis_tac[case_Literal]
            | "StructLit" => metis_tac[case_StructLit]
            | "Subscript" => ACCEPT_TAC case_Subscript
            | "Attribute" => ACCEPT_TAC case_Attribute
            | "Builtin" => ACCEPT_TAC case_Builtin
            | "TypeBuiltin" => ACCEPT_TAC case_TypeBuiltin
            | "Pop" => metis_tac[case_Pop]
            | "Call" =>
                (introduce >>
                 qpat_x_assum `pure_expr _` mp_tac >>
                 CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [pure_expr_def])) >>
                 simp_tac bool_ss [])
            | _ => FAIL_TAC "unknown pure-expression induction constructor"
      end g
  in
    mp_tac expr_state_ind_principle >>
    (impl_tac >- (rpt conj_tac >> dispatch)) >> simp[]
  end
*)
QED

Resume expr_state_mutual[TypeBuiltin]:
  rpt gen_tac >> strip_tac >> Cases_on `tb` >> gvs[] >>
  rpt strip_tac >>
  gvs[pure_expr_def, Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
    mark_abi_captures_def, ETA_THM] >>
  imp_res_tac lift_sum_state >> gvs[] >> res_tac >> gvs[] >>
  `state_rel_frame abi_append (eval_abi_exprs cx es)` by
    (simp[state_rel_frame_result] >> first_assum MATCH_ACCEPT_TAC) >>
  `!args. state_rel_frame abi_append (stage_abi_operands cx args)` by
    (gen_tac >> irule abi_append_readonly >> simp[abi_readonly_primitives]) >>
  `state_rel_frame abi_append
     (do args <- eval_abi_exprs cx es; stage_abi_operands cx args od)` by
    (irule state_rel_frame_bind_guarded >> simp[] >>
     metis_tac[abi_append_trans]) >>
  drule_all abi_append_finally_state >> simp[]
QED

Finalise expr_state_mutual

(* ------------------------------------------------------------------------
   Main Theorems

   Extracts the eval_expr/eval_exprs cases from the mutual induction.
   ------------------------------------------------------------------------ *)

Theorem eval_expr_preserves_state:
  ∀cx e st res st'.
    pure_expr e ∧ eval_expr cx e st = (res, st') ⇒
    st = st'
Proof
  metis_tac[expr_state_mutual]
QED

Theorem eval_exprs_preserves_state:
  ∀cx es st res st'.
    EVERY pure_expr es ∧ eval_exprs cx es st = (res, st') ⇒
    st = st'
Proof
  metis_tac[expr_state_mutual]
QED
