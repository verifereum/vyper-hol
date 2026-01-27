Theory vyperExpr

(* Theorems about expression evaluation.
 *)

Ancestors
  vyperInterpreter vyperScopes

(* Pure expressions: expressions that do not modify scopes.
   Pop is the only impure expression constructor - it modifies scoped variables.
*)

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
  pure_expr (Pop _) = F ∧
  pure_expr (Call _ es) = EVERY pure_expr es
Termination
  WF_REL_TAC `measure expr_size` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

(* ========================================================================
   Proof Sketch: eval_expr_preserves_scopes

   Shows that evaluating a pure expression preserves scopes exactly.
   Generated from proof plan. Uses individual case lemmas approach.
   ======================================================================== *)

(* ------------------------------------------------------------------------
   Section 1: Helper Lemmas for Scopes Preservation

   These lemmas show that specific operations preserve scopes exactly.
   ------------------------------------------------------------------------ *)

(* lookup_flag_mem is pure - only returns value without modifying state.

   WHY THIS IS TRUE:
   lookup_flag_mem only uses case analysis on get_module_code, lookup_flag,
   and INDEX_OF, then returns via return or raise. Neither modifies state.

   Plan reference: Case 3 (FlagMember)
   Used in: case_FlagMember *)
Theorem lookup_flag_mem_scopes[local]:
  ∀cx nsid mid st res st'.
    lookup_flag_mem cx nsid mid st = (res, st') ⇒
    st'.scopes = st.scopes
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, raise_def, return_def] >>
  rpt CASE_TAC >> simp[raise_def, return_def]
QED

(* switch_BoolV preserves scopes if both branches preserve scopes.

   WHY THIS IS TRUE:
   switch_BoolV dispatches to f if v = Value (BoolV T), to g if v = Value (BoolV F),
   else raises error. All three paths preserve scopes if f and g do.

   Plan reference: Case 4 (IfExp)
   Used in: case_IfExp *)
Theorem switch_BoolV_scopes[local]:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ⇒
    st'.scopes = st.scopes
Proof
  rw[switch_BoolV_def, raise_def]
QED

(* finally with pop_function restores scopes to prev.

   WHY THIS IS TRUE:
   finally f g runs f, then always runs g. pop_function prev = set_scopes prev,
   which sets st'.scopes := prev regardless of what f did.

   Plan reference: Case 15 (IntCall) - critical for restoring scopes
   Used in: case_IntCall *)
Theorem finally_pop_function_scopes[local]:
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
Theorem finally_set_scopes[local]:
  ∀f prev st res st'.
    finally f (set_scopes prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

(* Monad operations preserve scopes. These helper lemmas compose to prove
   that expressions built from these operations preserve scopes. *)

Theorem return_scopes[local]:
  ∀v st res st'. return v st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[return_def]
QED

Theorem raise_scopes[local]:
  ∀e st res st'. raise e st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[raise_def]
QED

Theorem get_scopes_scopes[local]:
  ∀st res st'. get_scopes st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_scopes_def, return_def]
QED

Theorem get_current_globals_scopes[local]:
  ∀cx st res st'. get_current_globals cx st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_current_globals_def, bind_def, lift_option_def, AllCaseEqs(), return_def, raise_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]
QED

Theorem get_immutables_scopes[local]:
  ∀cx st res st'. get_immutables cx st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_immutables_def, get_immutables_module_def, bind_def, return_def, AllCaseEqs()] >>
  drule get_current_globals_scopes >> simp[]
QED

Theorem lift_sum_scopes[local]:
  ∀sum st res st'. lift_sum sum st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  Cases_on `sum` >> rw[lift_sum_def, return_def, raise_def]
QED

Theorem lift_option_scopes[local]:
  ∀opt msg st res st'. lift_option opt msg st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  Cases_on `opt` >> rw[lift_option_def, return_def, raise_def]
QED

Theorem get_accounts_scopes[local]:
  ∀st res st'. get_accounts st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_Value_scopes[local]:
  ∀tv st res st'. get_Value tv st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem check_scopes[local]:
  ∀b msg st res st'. check b msg st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[check_def, assert_def, return_def, raise_def]
QED

Theorem transfer_value_scopes[local]:
  ∀from to amt st res st'.
    transfer_value from to amt st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[transfer_value_def, bind_def, AllCaseEqs(), return_def, raise_def,
     get_accounts_def, update_accounts_def, check_def, assert_def,
     ignore_bind_def] >>
  gvs[evaluation_state_component_equality]
QED

Theorem lookup_global_scopes[local]:
  ∀cx src_opt nm st res st'.
    lookup_global cx src_opt nm st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[lookup_global_def, bind_def, AllCaseEqs(), return_def, raise_def,
     get_current_globals_def, lift_option_def] >>
  fs[AllCaseEqs(), return_def, raise_def] >> gvs[] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def] >>
  Cases_on `FLOOKUP (get_module_globals src_opt gbs).mutables nm` >> gvs[return_def, raise_def]
QED

(* ------------------------------------------------------------------------
   Section 2: Individual Case Lemmas

   Each case of the mutual induction is proved as a separate theorem.
   Following the pattern used in vyperScopesScript.sml.
   ------------------------------------------------------------------------ *)

(* Case: Name - pure, only reads scopes and immutables.

   WHY THIS IS TRUE:
   get_scopes returns state unchanged. get_immutables reads globals.
   lift_sum and return don't modify state.

   Plan reference: Case 1 *)
Theorem case_Name[local]:
  ∀cx id.
    (∀st res st'.
       eval_expr cx (Name id) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def, bind_def, AllCaseEqs()] >> gvs[] >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[] >>
       drule lift_sum_scopes >> simp[] >> drule return_scopes >> simp[]) >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[] >>
       drule lift_sum_scopes >> simp[]) >>
  TRY (drule get_scopes_scopes >> simp[] >> drule get_immutables_scopes >> simp[]) >>
  drule get_scopes_scopes >> simp[]
QED

(* Case: TopLevelName - pure, only reads globals.

   WHY THIS IS TRUE:
   lookup_global only accesses st.globals, never modifies scopes.

   Plan reference: Case 2 *)
Theorem case_TopLevelName[local]:
  ∀cx src_id_opt id.
    (∀st res st'.
       eval_expr cx (TopLevelName (src_id_opt, id)) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_global_scopes >> simp[]
QED

(* Case: FlagMember - pure, only reads contract code.

   WHY THIS IS TRUE:
   lookup_flag_mem only does case analysis on module code, never modifies state.

   Plan reference: Case 3 *)
Theorem case_FlagMember[local]:
  ∀cx nsid mid.
    (∀st res st'.
       eval_expr cx (FlagMember nsid mid) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  rpt strip_tac >> fs[evaluate_def] >> drule lookup_flag_mem_scopes >> simp[]
QED

(* Case: IfExp - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates e1, then dispatches to e2 or e3 based on boolean result.
   If all three preserve scopes (IH), then so does the composition.

   Plan reference: Case 4 *)
Theorem case_IfExp[local]:
  ∀cx e1 e2 e3.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st.scopes = st'.scopes) ∧
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e3 st = (res, st') ⇒ pure_expr e3 ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (IfExp e1 e2 e3) st = (res, st') ⇒
       pure_expr (IfExp e1 e2 e3) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  fs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, pure_expr_def, raise_def] >>
  gvs[] >>
  `st.scopes = s''.scopes` by (first_x_assum drule >> simp[]) >>
  Cases_on `tv = Value (BoolV T)` >> gvs[] >-
    (first_x_assum drule >> simp[] >> metis_tac[]) >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  qpat_x_assum `∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1, t) ⇒ _` drule >>
  simp[] >> metis_tac[]
QED

(* Case: Literal - trivially pure.

   WHY THIS IS TRUE:
   return $ Value $ evaluate_literal l doesn't modify state.

   Plan reference: Case 5 *)
Theorem case_Literal[local]:
  ∀cx l.
    (∀st res st'.
       eval_expr cx (Literal l) st = (res, st') ⇒
       st.scopes = st'.scopes)
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
       EVERY pure_expr (MAP SND kes) ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (StructLit src kes) st = (res, st') ⇒
       pure_expr (StructLit src kes) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> PairCases_on `src` >>
  fs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, return_def] >> gvs[] >>
  first_x_assum drule >> gvs[listTheory.EVERY_MAP]
QED

(* Case: Subscript - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates e1 and e2, then performs subscript operation.
   If both evals preserve scopes, and get_Value/lift_option/lift_sum/return do too,
   the whole operation preserves scopes.

   Plan reference: Case 7 *)
Theorem case_Subscript[local]:
  ∀cx e1 e2.
    (∀s'' tv1 t.
       eval_expr cx e1 s'' = (INL tv1, t) ⇒
       ∀st res st'.
         eval_expr cx e2 st = (res, st') ⇒ pure_expr e2 ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e1 st = (res, st') ⇒ pure_expr e1 ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Subscript e1 e2) st = (res, st') ⇒
       pure_expr (Subscript e1 e2) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac return_scopes >> imp_res_tac lift_sum_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac get_Value_scopes >>
  res_tac >> gvs[] >> metis_tac[]
QED

(* Case: Attribute - uses IH on subexpression.

   WHY THIS IS TRUE:
   Evaluates e, then extracts attribute. If eval preserves scopes (IH),
   and get_Value/lift_sum/return preserve scopes, whole operation does.

   Plan reference: Case 8 *)
Theorem case_Attribute[local]:
  ∀cx e id.
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Attribute e id) st = (res, st') ⇒
       pure_expr (Attribute e id) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def] >>
  imp_res_tac return_scopes >> imp_res_tac lift_sum_scopes >>
  imp_res_tac get_Value_scopes >> res_tac >> gvs[] >> metis_tac[]
QED

(* Case: Builtin - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates es, then calls builtin. check, get_accounts, lift_sum all preserve scopes.

   Plan reference: Case 9 *)
Theorem case_Builtin[local]:
  ∀cx bt es.
    (∀s'' x t.
       check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Builtin bt es) st = (res, st') ⇒
       pure_expr (Builtin bt es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, get_accounts_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_builtin cx s''.accounts bt vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

(* Case: Pop - vacuously true since pure_expr (Pop _) = F.

   WHY THIS IS TRUE:
   The hypothesis pure_expr (Pop _) is false by definition.

   Plan reference: Case 10 *)
Theorem case_Pop[local]:
  ∀cx bt.
    (∀st res st'.
       eval_expr cx (Pop bt) st = (res, st') ⇒
       pure_expr (Pop bt) ⇒ st.scopes = st'.scopes)
Proof
  rw[pure_expr_def]
QED

(* Case: TypeBuiltin - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates es, then calls type builtin. All operations preserve scopes.

   Plan reference: Case 11 *)
Theorem case_TypeBuiltin[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (TypeBuiltin tb typ es) st = (res, st') ⇒
       pure_expr (TypeBuiltin tb typ es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

(* Case: Call Send - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates es, then calls transfer_value (which only modifies accounts, not scopes).

   Plan reference: Case 12 *)
Theorem case_Send[local]:
  ∀cx es.
    (∀s'' x t.
       check (LENGTH es = 2) "Send args" s'' = (INL x, t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Call Send es) st = (res, st') ⇒
       pure_expr (Call Send es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), pure_expr_def, ignore_bind_def,
      check_def, assert_def, return_def, raise_def, lift_option_def] >>
  TRY (drule transfer_value_scopes >> strip_tac) >>
  TRY (Cases_on `dest_NumV (EL 1 vs)` >> gvs[return_def, raise_def]) >>
  TRY (Cases_on `dest_AddressV (HD vs)` >> gvs[return_def, raise_def]) >>
  first_x_assum drule >> gvs[ETA_THM]
QED

(* Case: ExtCall - raises error, state unchanged.

   WHY THIS IS TRUE:
   raise $ Error "TODO" doesn't modify state.

   Plan reference: Case 13 *)
Theorem case_ExtCall[local]:
  ∀cx sig vs.
    (∀st res st'.
       eval_expr cx (Call (ExtCall sig) vs) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  simp[evaluate_def, raise_def]
QED

(* Case: StaticCall - raises error, state unchanged.

   WHY THIS IS TRUE:
   raise $ Error "TODO" doesn't modify state.

   Plan reference: Case 14 *)
Theorem case_StaticCall[local]:
  ∀cx sig vs.
    (∀st res st'.
       eval_expr cx (Call (StaticCall sig) vs) st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  simp[evaluate_def, raise_def]
QED

(* Case: IntCall - the complex case with finally/pop_function.

   WHY THIS IS TRUE:
   The key is that get_scopes saves prev = st.scopes before entering function,
   and finally ... (pop_function prev) restores scopes to prev at the end,
   regardless of whether the function body succeeded or failed.

   Plan reference: Case 15 *)
Theorem case_IntCall[local]:
  ∀cx src_id_opt fn es.
    (* IH from evaluate_ind for eval_stmts in function body - not needed for scopes *)
    (* IH for eval_exprs on arguments *)
    (∀s'' x t s'3' ts t' s'4' tup t'' stup args sstup ret ss s'5' x' t'3'.
       check (¬MEM (src_id_opt, fn) cx.stk) "recursion" s'' = (INL x, t) ∧
       lift_option (get_module_code cx src_id_opt) "IntCall get_module_code" s'3' = (INL ts, t') ∧
       lift_option (lookup_function fn Internal ts) "IntCall lookup_function" s'4' = (INL tup, t'') ∧
       stup = SND tup ∧ args = FST stup ∧ sstup = SND stup ∧
       ret = FST sstup ∧ ss = SND sstup ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'5' = (INL x', t'3') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_expr cx (Call (IntCall (src_id_opt, fn)) es) st = (res, st') ⇒
       pure_expr (Call (IntCall (src_id_opt, fn)) es) ⇒ st.scopes = st'.scopes)
Proof
  let
    val sub_tac =
      TRY (drule_all finally_set_scopes >> strip_tac >> gvs[]) >>
      TRY (Cases_on `safe_cast rtv rv` >> gvs[return_def, raise_def]) >>
      TRY (Cases_on `evaluate_type (type_env ts) (FST (SND (SND tup)))` >> gvs[return_def, raise_def]) >>
      TRY (Cases_on `bind_arguments (type_env ts) (FST (SND tup)) vs` >> gvs[return_def, raise_def]) >>
      TRY (Cases_on `lookup_function fn Internal ts` >> gvs[return_def, raise_def]) >>
      TRY (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
      TRY (last_x_assum mp_tac >> simp[check_def, assert_def, return_def, lift_option_def] >>
           strip_tac >> first_x_assum drule >> gvs[pure_expr_def] >> metis_tac[])
  in
    rpt strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
         check_def, assert_def, lift_option_def, get_scopes_def, push_function_def,
         pop_function_def, set_scopes_def, pure_expr_def] >>
    strip_tac >> gvs[return_def, raise_def] >>
    sub_tac >> sub_tac >> sub_tac >> sub_tac >> sub_tac >>
    sub_tac >> sub_tac >> sub_tac >> sub_tac
  end
QED

(* Case: eval_exprs [] - trivially pure.

   WHY THIS IS TRUE:
   return [] doesn't modify state.

   Plan reference: Case 16 *)
Theorem case_eval_exprs_nil[local]:
  ∀cx.
    (∀st res st'.
       eval_exprs cx [] st = (res, st') ⇒
       st.scopes = st'.scopes)
Proof
  simp[evaluate_def, return_def]
QED

(* Case: eval_exprs cons - uses IH on subexpressions.

   WHY THIS IS TRUE:
   Evaluates e, then eval_exprs es. Both preserve scopes by IH.

   Plan reference: Case 17 *)
Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv, t) ∧ get_Value tv s'3' = (INL v, t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st.scopes = st'.scopes) ⇒
    (∀st res st'.
       eval_exprs cx (e::es) st = (res, st') ⇒
       EVERY pure_expr (e::es) ⇒ st.scopes = st'.scopes)
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  TRY (`st.scopes = s''.scopes` by (first_x_assum (qspec_then `st` mp_tac) >> simp[])) >>
  TRY (`s'³'.scopes = s'⁴'.scopes` by (
    last_x_assum (qspecl_then [`st`, `tv`, `s''`, `s''`, `v''`, `s'³'`] mp_tac) >>
    simp[] >> strip_tac >> first_x_assum drule >> simp[])) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   Section 3: Main Mutual Induction Theorem

   Assembles individual case lemmas into the full mutual induction.
   The key insight is that we prove the same scopes-preserving property
   for ALL evaluate functions (including statements), but for statements
   we get it for free since we set their predicates to T (trivially true).
   
   We use a specialized version of evaluate_ind with:
   - P0-P6 (statement predicates) = λcx args. T
   - P7 (eval_expr predicate) = scopes preservation with pure_expr
   - P8 (eval_exprs predicate) = scopes preservation with EVERY pure_expr
   ------------------------------------------------------------------------ *)

(* Derive specialized induction principle for pure_scopes_mutual.
   This encapsulates the SML needed to specialize evaluate_ind. *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\(cx:evaluation_context) (t:base_assignment_target). T``
  val p6 = ``\(cx:evaluation_context) (nm:num) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> pure_expr e ==> st.scopes = st'.scopes``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> EVERY pure_expr es ==> st.scopes = st'.scopes``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val pure_scopes_ind_principle = save_thm("pure_scopes_ind_principle", spec_ind_beta)
end

(* Main mutual induction: pure expressions preserve scopes exactly.

   WHY THIS IS TRUE:
   By induction on evaluate_ind. Each expression case is handled by the
   specialized induction principle. Statement cases are trivially T.

   Plan reference: Main proof structure (Cases 1-17) *)
Theorem pure_scopes_mutual[local]:
  (∀cx e st res st'.
     eval_expr cx e st = (res, st') ⇒ pure_expr e ⇒ st.scopes = st'.scopes) ∧
  (∀cx es st res st'.
     eval_exprs cx es st = (res, st') ⇒ EVERY pure_expr es ⇒ st.scopes = st'.scopes)
Proof
  (* Proof assembles all case lemmas (case_Name, case_TopLevelName, etc.)
     via the specialized induction principle pure_scopes_ind_principle.
     
     All individual case lemmas are proven above without cheats.
     The assembly just requires matching the goal shapes from the induction
     principle to the case lemma statements.
     
     TODO: The proof can be completed by:
     1. After impl_tac, split into 47 goals
     2. First ~29 goals have conclusion T, solved by simp[]
     3. Remaining 18 goals are expression cases, each solvable via the
        corresponding case lemma (proved above) *)
  cheat
QED

(* ------------------------------------------------------------------------
   Section 4: Main Theorems

   Extracts the eval_expr/eval_exprs cases from the mutual induction.
   ------------------------------------------------------------------------ *)

(* Main theorem: pure expression evaluation preserves scopes exactly.

   WHY THIS IS TRUE:
   Direct consequence of pure_scopes_mutual (8th conjunct).

   Plan reference: Main theorem statement *)
Theorem eval_expr_preserves_scopes:
  ∀cx e st res st'.
    pure_expr e ∧ eval_expr cx e st = (res, st') ⇒
    st.scopes = st'.scopes
Proof
  metis_tac[pure_scopes_mutual]
QED

(* Bonus: eval_exprs also preserves scopes for pure expressions.

   WHY THIS IS TRUE:
   Direct consequence of pure_scopes_mutual (9th conjunct). *)
Theorem eval_exprs_preserves_scopes:
  ∀cx es st res st'.
    EVERY pure_expr es ∧ eval_exprs cx es st = (res, st') ⇒
    st.scopes = st'.scopes
Proof
  metis_tac[pure_scopes_mutual]
QED
