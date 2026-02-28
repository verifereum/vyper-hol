Theory vyperPureExpr
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter vyperLookup vyperStatePreservation

(* Pure expressions: expressions that do not modify state. *)
Definition pure_expr_def:
  pure_expr (Name _) = T ∧
  pure_expr (TopLevelName _) = T ∧
  pure_expr (FlagMember _ _) = T ∧
  pure_expr (Literal _) = T ∧
  pure_expr (IfExp e1 e2 e3) = (pure_expr e1 ∧ pure_expr e2 ∧ pure_expr e3) ∧
  pure_expr (StructLit _ kes) = EVERY pure_expr (MAP SND kes) ∧
  pure_expr (Subscript e1 e2) = (pure_expr e1 ∧ pure_expr e2) ∧
  pure_expr (Attribute e _) = pure_expr e ∧
  pure_expr (Builtin _ es) = EVERY pure_expr es ∧
  pure_expr (TypeBuiltin _ _ es) = EVERY pure_expr es ∧
  pure_expr _ = F
Termination
  WF_REL_TAC `measure expr_size` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

(* ------------------------------------------------------------------------
   Individual Case Lemmas
   ------------------------------------------------------------------------ *)

Theorem case_Name[local]:
  ∀cx id.
    (∀st res st'.
       eval_expr cx (Name id) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), get_scopes_def, return_def] >>
  imp_res_tac get_immutables_state >> imp_res_tac lift_sum_state >> gvs[]
QED

Theorem case_TopLevelName[local]:
  ∀cx src_id_opt id.
    (∀st res st'.
       eval_expr cx (TopLevelName (src_id_opt, id)) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_global_state >> simp[]
QED

Theorem case_FlagMember[local]:
  ∀cx nsid mid.
    (∀st res st'.
       eval_expr cx (FlagMember nsid mid) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_flag_mem_state >> simp[]
QED

Theorem case_IfExp[local]:
  ∀cx e1 e2 e3.
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
       eval_expr cx (IfExp e1 e2 e3) st = (res, st') ⇒
       pure_expr (IfExp e1 e2 e3) ⇒ st = st')
Proof
  rpt strip_tac >>
  fs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, pure_expr_def, raise_def] >>
  gvs[] >>
  `st = s''` by (first_x_assum drule >> simp[]) >>
  Cases_on `tv = Value (BoolV T)` >> gvs[] >-
    (first_x_assum drule >> simp[] >> metis_tac[]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  qpat_x_assum `∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1, t) ⇒ _` drule >>
  simp[]
QED

Theorem case_Literal[local]:
  ∀cx l.
    (∀st res st'.
       eval_expr cx (Literal l) st = (res, st') ⇒
       st = st')
Proof
  rpt strip_tac >> fs[evaluate_def, return_def]
QED

(* Case: StructLit - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates MAP SND kes as expressions, then constructs struct.
   If eval_exprs preserves scopes (IH), result preserves scopes.

   Plan reference: Case 6 *)
Theorem case_StructLit[local]:
  ∀cx src kes.
    (∀st res st'.
       eval_exprs cx (MAP SND kes) st = (res, st') ⇒
       EVERY pure_expr (MAP SND kes) ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (StructLit src kes) st = (res, st') ⇒
       pure_expr (StructLit src kes) ⇒ st = st')
Proof
  rpt strip_tac >> PairCases_on `src` >>
  fs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, return_def] >> gvs[] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> gvs[listTheory.EVERY_MAP]
QED

Theorem case_Subscript[local]:
  ∀cx e1 e2.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st = st') ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (Subscript e1 e2) st = (res, st') ⇒
       pure_expr (Subscript e1 e2) ⇒ st = st')
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac return_state >> imp_res_tac lift_sum_state >>
  imp_res_tac lift_option_state >> imp_res_tac get_Value_state >>
  imp_res_tac lift_sum_state >>
  gvs[check_array_bounds_def, bind_def, ignore_bind_def, AllCaseEqs(),
      check_def, type_check_def, assert_def, return_def, raise_def] >>
  imp_res_tac get_storage_backend_state >>
  gvs[return_def, bind_def, AllCaseEqs(), sum_CASE_rator, prod_CASE_rator] >>
  imp_res_tac return_state >> imp_res_tac lift_sum_state >>
  imp_res_tac lift_option_state >> imp_res_tac get_Value_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac get_Value_state >>
  imp_res_tac read_storage_slot_state >>
  imp_res_tac check_array_bounds_state >>
  gvs[] >>
  metis_tac []
QED

Theorem case_Attribute[local]:
  ∀cx e id.
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (Attribute e id) st = (res, st') ⇒
       pure_expr (Attribute e id) ⇒ st = st')
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac return_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_Value_state >> res_tac >> gvs[]
QED

Theorem case_Builtin[local]:
  ∀cx bt es.
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
       eval_expr cx (Builtin bt es) st = (res, st') ⇒
       pure_expr (Builtin bt es) ⇒ st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def, get_accounts_def, lift_sum_def] >>
  Cases_on `bt = Len` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def]
  (* Len case: eval_expr (HD es) + toplevel_array_length *)
  (* Len case *)
  >- (gvs[toplevel_array_length_def, bind_def, AllCaseEqs(),
          return_def, raise_def, get_accounts_def] >>
      imp_res_tac get_storage_backend_state >> gvs[] >>
      imp_res_tac check_array_bounds_state >> gvs[] >>
      imp_res_tac materialise_state >> gvs[] >>
      imp_res_tac toplevel_array_length_state >>
      `pure_expr (HD es)` by
        (Cases_on `es` >> fs[builtin_args_length_ok_def]) >>
      first_x_assum drule >> gvs[])
  (* non-Len case: eval_exprs + evaluate_builtin *)
  >> TRY (Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM, sum_CASE_rator, CaseEq"sum",
    return_def, raise_def, get_accounts_def, builtin_args_length_ok_def,
    listTheory.LENGTH_EQ_NUM_compute] >>
  imp_res_tac toplevel_array_length_state >> gvs[]
QED

Theorem case_Pop[local]:
  ∀cx bt.
    (∀st res st'.
       eval_expr cx (Pop bt) st = (res, st') ⇒
       pure_expr (Pop bt) ⇒ st = st')
Proof
  rw[pure_expr_def]
QED

Theorem case_TypeBuiltin[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ⇒
    (∀st res st'.
       eval_expr cx (TypeBuiltin tb typ es) st = (res, st') ⇒
       pure_expr (TypeBuiltin tb typ es) ⇒ st = st')
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

(* All Call cases are vacuously true since pure_expr (Call _ _ _) = F *)
Theorem case_Call[local]:
  ∀cx c es drv st res st'.
    eval_expr cx (Call c es drv) st = (res, st') ⇒
    pure_expr (Call c es drv) ⇒ st = st'
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
       eval_expr cx e s'' = (INL tv, t) ∧ materialise cx tv s'3' = (INL v, t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st') ∧
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ⇒
    (∀st res st'.
       eval_exprs cx (e::es) st = (res, st') ⇒
       EVERY pure_expr (e::es) ⇒ st = st')
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac materialise_state >> gvs[] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Main Mutual Induction Theorem

   Assembles individual case lemmas into the full mutual induction.
   The key insight is that we prove the same scopes-preserving property
   for ALL evaluate functions (including statements), but for statements
   we get it for free since we set their predicates to T (trivially true).

   We use a specialized version of evaluate_ind with:
   - P0-P6 (statement predicates) = λcx args. T
   - P7 (eval_expr predicate) = scopes preservation with pure_expr
   - P8 (eval_exprs predicate) = scopes preservation with EVERY pure_expr
   ------------------------------------------------------------------------ *)

(* Derive specialized induction principle for expr_state_mutual.
   This encapsulates the SML needed to specialize evaluate_ind. *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p6 = ``\(cx:evaluation_context) (nm:num) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> pure_expr e ==> st = st'``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY pure_expr es ==> st = st'``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val expr_state_ind_principle = save_thm("expr_state_ind_principle", spec_ind_beta)
end

(* Main mutual induction. *)
Theorem expr_state_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st = st') ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st = st')
Proof
  MP_TAC expr_state_ind_principle >> impl_tac >- (
    rpt conj_tac >>
    (* Close trivially-T subgoals (P0-P6) and all Call/Pop cases
       (pure_expr (Call _ _ _) = F makes conclusion vacuous) *)
    TRY (simp[pure_expr_def] >> NO_TAC) >-
    metis_tac[case_Name] >-
    metis_tac[case_TopLevelName] >-
    metis_tac[case_FlagMember] >-
    ACCEPT_TAC case_IfExp >-
    metis_tac[case_Literal] >-
    metis_tac[case_StructLit] >-
    ACCEPT_TAC case_Subscript >-
    ACCEPT_TAC case_Attribute >-
    ACCEPT_TAC case_Builtin >-
    ACCEPT_TAC case_TypeBuiltin >-
    metis_tac[case_eval_exprs_nil] >-
    ACCEPT_TAC case_eval_exprs_cons
  ) >>
  simp[]
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
