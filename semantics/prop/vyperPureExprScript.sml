Theory vyperPureExpr
Ancestors
  vyperExprEffects vyperMisc vyperContext vyperState vyperStorageBackend
  vyperInterpreter vyperLookup vyperStatePreservation vyperPlaceFrames

(* Pure expressions preserve runtime state while storage observations grow.
   msg.gas consumes a gas reading, and precompiles consume a call outcome.
   The shared syntax definition spells precompiles out; restate that here. *)
Theorem precompile_builtin_exclusion[local]:
  !bt P. bt <> Sha256 /\ bt <> ECRecover /\ bt <> ECAdd /\ bt <> ECMul /\ P <=>
         ~precompile_builtin bt /\ P
Proof
  Cases >> simp[]
QED

Theorem pure_expr_def =
  REWRITE_RULE [precompile_builtin_exclusion]
    vyperExprEffectsTheory.pure_expr_def;

(* Specialize the canonical evaluator induction theorem. Only expression
   and expression-list evaluation carry whole-state preservation obligations. *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:eval_result list). T``
  val p4 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> pure_expr e ==> st' = st with storage_trace := st'.storage_trace``
  val p5 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY pure_expr es ==> st' = st with storage_trace := st'.storage_trace``
  val p6 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p7 = p6
  val p8 = ``\(cx:evaluation_context) (g:assignment_target) (v:value). T``
  val p9 = ``\(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T``
in
  val expr_state_ind_principle =
    CONV_RULE (DEPTH_CONV BETA_CONV)
      (SPECL [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9] evaluate_ind)
end

Theorem trace_state_trans[local]:
  (b = a with storage_trace := b.storage_trace) /\
  (c = b with storage_trace := c.storage_trace) ==>
  c = a with storage_trace := c.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `c = _` mp_tac >>
  qpat_x_assum `b = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* ------------------------------------------------------------------------
   Individual Case Lemmas
   ------------------------------------------------------------------------ *)

Theorem case_Name[local]:
  ∀cx ty id.
    (∀st res st'.
       eval_expr cx (Name ty id) st = (res, st') ⇒
       st' = st with storage_trace := st'.storage_trace)
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
       st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_global_state >> simp[]
QED

Theorem case_FlagMember[local]:
  ∀cx ty nsid mid.
    (∀st res st'.
       eval_expr cx (FlagMember ty nsid mid) st = (res, st') ⇒
       st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_flag_mem_state >> simp[]
QED

Theorem case_IfExp[local]:
  ∀cx ty e1 e2 e3.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st' = st with storage_trace := st'.storage_trace) ∧
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e3 st = (res, st') ⇒ pure_expr e3 ⇒ st' = st with storage_trace := st'.storage_trace) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_expr cx (IfExp ty e1 e2 e3) st = (res, st') ⇒
       pure_expr (IfExp ty e1 e2 e3) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def,
      pure_expr_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
  metis_tac[trace_state_trans]
QED

Theorem case_Literal[local]:
  ∀cx ty l.
    (∀st res st'.
       eval_expr cx (Literal ty l) st = (res, st') ⇒
       st' = st with storage_trace := st'.storage_trace)
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
       EVERY pure_expr (MAP SND kes) ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_expr cx (StructLit ty src kes) st = (res, st') ⇒
       pure_expr (StructLit ty src kes) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >> PairCases_on `src` >>
  fs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, return_def] >> gvs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> gvs[listTheory.EVERY_MAP]
QED

Theorem case_Subscript[local]:
  ∀cx ty e1 e2.
    (∀s'' tv1 t s''' tv1' t'.
       eval_expr cx e1 s'' = (INL tv1, t) ∧
       (if subscript_reads_base cx e1 e2 then
          do v <- read_result cx tv1; return (Value v) od
        else return tv1) s''' = (INL tv1', t') ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st' = st with storage_trace := st'.storage_trace) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_expr cx (Subscript ty e1 e2) st = (res, st') ⇒
       pure_expr (Subscript ty e1 e2) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  rpt (qpat_x_assum `!s res t s' res' t'. _` drule_all >> strip_tac) >>
  Cases_on `subscript_reads_base cx e1 e2` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[trace_state_trans]
QED

Theorem case_Attribute[local]:
  ∀cx ty e id.
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_expr cx (Attribute ty e id) st = (res, st') ⇒
       pure_expr (Attribute ty e id) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[trace_state_trans]
QED

(* The Builtin hypothesis of expr_state_ind_principle, selected by its
   conclusion so it tracks the evaluator's induction hypotheses. *)
val builtin_state_case = let
  fun spine tm =
    if is_forall tm then spine (snd (dest_forall tm))
    else if is_imp tm then
      let val (a,b) = dest_imp tm in
        if is_comb a andalso same_const (fst (strip_comb a)) ``pure_expr``
        then SOME a else spine b
      end
    else NONE
  fun is_builtin tm =
    case spine tm of
      NONE => false
    | SOME p => same_const (fst (strip_comb (rand p))) ``Builtin``
  val cases = strip_conj (fst (dest_imp (concl expr_state_ind_principle)))
in
  case List.filter is_builtin cases of [tm] => tm
  | _ => raise Fail "expected unique Builtin preservation case"
end;

Theorem case_Builtin[local]:
  ^builtin_state_case
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Len`
  >- (rpt strip_tac >> gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      strip_tac >> gvs[return_def] >>
      imp_res_tac result_array_length_state >> gvs[] >>
      `pure_expr (HD es)` by
        (Cases_on `es` >> gvs[builtin_args_length_ok_def]) >>
      fs[type_check_def, assert_def, return_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[pure_expr_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)` >>
  fs[type_check_def, assert_def, return_def, raise_def, ignore_bind_def,
     bind_def] >>
  simp[AllCaseEqs(), return_def] >> strip_tac >> gvs[return_def] >>
  imp_res_tac get_accounts_state >> imp_res_tac if_lift_sum_state >> gvs[]
  >>~- ([`option_CASE (code_slice_source _ _) _ _ _ = _`],
        drule_at (Pos last) builtin_operands_preserve >>
        disch_then (qspec_then
          `\a b. b = a with storage_trace := b.storage_trace` mp_tac) >>
        simp[] >>
        impl_tac
        >- (rw[] >>
            gvs[code_slice_source_SOME, pure_expr_def, precompile_builtin_def] >>
            metis_tac[trace_state_trans]) >>
        gvs[])
QED

Theorem case_Pop[local]:
  ∀cx ty bt.
    (∀st res st'.
       eval_expr cx (Pop ty bt) st = (res, st') ⇒
       pure_expr (Pop ty bt) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rw[pure_expr_def]
QED

Theorem case_TypeBuiltin[local]:
  ∀cx ty tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_expr cx (TypeBuiltin ty tb typ es) st = (res, st') ⇒
       pure_expr (TypeBuiltin ty tb typ es) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >>
  metis_tac[]
QED

Theorem case_eval_exprs_nil[local]:
  ∀cx.
    (∀st res st'.
       eval_exprs cx [] st = (res, st') ⇒
       st' = st with storage_trace := st'.storage_trace)
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv, t) ∧ read_result cx tv s'3' = (INL v, t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st' = st with storage_trace := st'.storage_trace) ∧
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st' = st with storage_trace := st'.storage_trace) ⇒
    (∀st res st'.
       eval_exprs cx (e::es) st = (res, st') ⇒
       EVERY pure_expr (e::es) ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  qpat_assum `!s r t. eval_expr cx e s = (r,t) ==> _`
    (drule_then assume_tac) >>
  rename1 `eval_expr cx e start = (INL value,mid)` >>
  rename1 `read_result cx value mid = (INL read_value,mid)` >>
  rename1 `eval_exprs cx es mid = (result,finish)` >>
  `finish = mid with storage_trace := finish.storage_trace` by
    (first_x_assum (qspecl_then
       [`start`,`value`,`mid`,`mid`,`read_value`,`mid`] mp_tac) >>
     simp[] >>
     disch_then (qspecl_then [`mid`,`result`,`finish`] mp_tac) >> simp[]) >>
  irule trace_state_trans >> qexists_tac `mid` >> simp[]
QED

(* ------------------------------------------------------------------------
   Main Mutual Induction Theorem

   Assembles individual case lemmas into the full mutual induction.
   The canonical ten-function specialization assigns whole-state preservation
   to P4 (eval_expr) and P5 (eval_exprs), and T to every other predicate.
   Dispatch examines only the conclusion spine, never the guarded IHs.
   ------------------------------------------------------------------------ *)

(* expr_state_ind_principle is specialized above the constructor lemmas. *)

(* Main mutual induction. *)
Theorem expr_state_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st' = st with storage_trace := st'.storage_trace) ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st' = st with storage_trace := st'.storage_trace)
Proof
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
            | "Builtin" => suspend "builtin"
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
QED

Resume expr_state_mutual[builtin]:
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `ty`, `bt`, `es`] mp_tac case_Builtin >>
  (impl_tac >- metis_tac[]) >>
  simp[]
QED

Finalise expr_state_mutual

(* ------------------------------------------------------------------------
   Main Theorems

   Extracts the eval_expr/eval_exprs cases from the mutual induction.
   ------------------------------------------------------------------------ *)

Theorem eval_expr_preserves_state:
  ∀cx e st res st'.
    pure_expr e ∧ eval_expr cx e st = (res, st') ⇒
    st' = st with storage_trace := st'.storage_trace
Proof
  metis_tac[expr_state_mutual]
QED

Theorem eval_exprs_preserves_state:
  ∀cx es st res st'.
    EVERY pure_expr es ∧ eval_exprs cx es st = (res, st') ⇒
    st' = st with storage_trace := st'.storage_trace
Proof
  metis_tac[expr_state_mutual]
QED
