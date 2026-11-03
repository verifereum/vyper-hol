Theory vyperPureExpr
Ancestors
  vyperMisc vyperContext vyperState vyperStorageBackend vyperInterpreter vyperLookup vyperStatePreservation vyperPlaceFrames

(* Pure expressions: expressions that do not modify state.  msg.gas is not
   pure: it consumes a gas reading. *)
Definition pure_expr_def:
  pure_expr (Name _ _) = T ∧
  pure_expr (TopLevelName _ _) = T ∧
  pure_expr (FlagMember _ _ _) = T ∧
  pure_expr (Literal _ _) = T ∧
  pure_expr (IfExp _ e1 e2 e3) = (pure_expr e1 ∧ pure_expr e2 ∧ pure_expr e3) ∧
  pure_expr (StructLit _ _ kes) = EVERY pure_expr (MAP SND kes) ∧
  pure_expr (Subscript _ e1 e2) = (pure_expr e1 ∧ pure_expr e2) ∧
  pure_expr (Attribute _ e _) = pure_expr e ∧
  pure_expr (Builtin _ bt es) = (bt ≠ Env MsgGas ∧ EVERY pure_expr es) ∧
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
in
  val expr_state_ind_principle =
    CONV_RULE (DEPTH_CONV BETA_CONV)
      (SPECL [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10] evaluate_ind)
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

(* Select the exact generated case by its conclusion, not its position. *)
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
  val matches = List.filter is_builtin cases
in
  case matches of [tm] => tm
  | _ => raise Fail "expected unique Builtin preservation case"
end;

(* Simplify guarded IHs independently: never cross-rewrite the IH bank. *)
fun builtin_branch_normalize (g as (asl,_)) = let
  fun guarded tm = is_forall tm orelse (is_imp tm andalso not (is_neg tm))
  val facts = map ASSUME (List.filter (not o guarded) asl)
  fun norm th = if guarded (concl th)
    then SIMP_RULE (srw_ss()) facts th else th
in
  (RULE_ASSUM_TAC norm >> rpt (qpat_x_assum `T` kall_tac) >>
   simp_tac (srw_ss()) facts) g
end;

Theorem case_Builtin[local]:
  ^builtin_state_case
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Len`
  >- (qpat_assum `bt = Len` (fn eq =>
        RULE_ASSUM_TAC (SIMP_RULE bool_ss [eq]) >> assume_tac eq) >>
      rpt (qpat_x_assum `T` kall_tac) >>
      rpt strip_tac >>
      gvs[Once evaluate_def, pure_expr_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >> gvs[] >>
      `pure_expr (HD es)` by
        (Cases_on `es` >> gvs[builtin_args_length_ok_def]) >>
      metis_tac[type_check_def, assert_def, return_def]) >>
  rpt gen_tac >> disch_tac >> disch_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss())
    [pure_expr_def, type_check_def, assert_def, return_def]) >>
  rpt (qpat_x_assum `T` kall_tac) >>
  qpat_x_assum `eval_expr _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
  simp_tac (srw_ss())
    [bind_def, ignore_bind_def, type_check_def, assert_def, return_def,
     raise_def] >>
  qpat_x_assum `bt <> Env MsgGas /\ _` strip_assume_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (builtin_branch_normalize >>
      Cases_on `bt` >> builtin_branch_normalize
      >~ [`Slice n`] >- suspend "slice"
      >> gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
             return_def, raise_def, AllCaseEqs()] >>
      gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      metis_tac[]) >>
  builtin_branch_normalize >> simp[]
QED

Resume case_Builtin[slice]:
  qpat_x_assum `builtin_args_length_ok _ _` mp_tac >>
  simp_tac (srw_ss()) [builtin_args_length_ok_def, listTheory.LENGTH_EQ_NUM_compute] >>
  strip_tac >>
  rpt (qpat_x_assum `(_:expr list) = _` SUBST_ALL_TAC) >>
  builtin_branch_normalize >>
  rename1 `EVERY _ [first; start; len]` >>
  Cases_on `first` >> builtin_branch_normalize
  >~ [`Builtin code_ty inner args`] >- suspend "slice_builtin"
  >> gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
         return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Resume case_Builtin[slice_builtin]:
  Cases_on `inner` >> builtin_branch_normalize
  >~ [`Acc acc`] >- suspend "slice_acc"
  >> gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
         return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Resume case_Builtin[slice_acc]:
  Cases_on `acc` >> builtin_branch_normalize
  >~ [`Acc Code`] >- suspend "slice_code"
  >> gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
         return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Resume case_Builtin[slice_code]:
  namedCases_on `args` ["", "addr rest"] >> builtin_branch_normalize
  >- (gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
          return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
      gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]) >>
  Cases_on `rest` >> builtin_branch_normalize
  >- (gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
          return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
      gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]) >>
  gvs[bind_def, ignore_bind_def, get_accounts_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs(), pure_expr_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Finalise case_Builtin

Theorem case_Pop[local]:
  ∀cx ty bt.
    (∀st res st'.
       eval_expr cx (Pop ty bt) st = (res, st') ⇒
       pure_expr (Pop ty bt) ⇒ st = st')
Proof
  rw[pure_expr_def]
QED

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
   The canonical ten-function specialization assigns whole-state preservation
   to P4 (eval_expr) and P5 (eval_exprs), and T to every other predicate.
   Dispatch examines only the conclusion spine, never the guarded IHs.
   ------------------------------------------------------------------------ *)

(* expr_state_ind_principle is specialized above the constructor lemmas. *)

(* Main mutual induction. *)
Theorem expr_state_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st')
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
QED

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
