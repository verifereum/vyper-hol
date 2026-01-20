Theory vyperScopes

Ancestors
  vyperInterpreter

(* ===== Helper lemmas for scopes length preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_scopes[local]:
  !x st res st'. return x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[return_def]
QED

Theorem raise_scopes[local]:
  !e st res st'. raise e st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[raise_def]
QED

Theorem check_scopes[local]:
  !b s st res st'. check b s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[check_def, assert_def]
QED

Theorem lift_option_scopes[local]:
  !x s st res st'. lift_option x s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_scopes[local]:
  !x st res st'. lift_sum x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_scopes[local]:
  !tv st res st'. get_Value tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_scopes_id[local]:
  !st res st'. get_scopes st = (res, st') ==> st' = st
Proof
  rw[get_scopes_def, return_def]
QED

Theorem get_accounts_scopes[local]:
  !st res st'. get_accounts st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_current_globals_scopes[local]:
  !cx st res st'. get_current_globals cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem set_current_globals_scopes[local]:
  !cx gbs st res st'. set_current_globals cx gbs st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_current_globals_def, return_def] >> simp[]
QED

Theorem get_immutables_scopes[local]:
  !cx st res st'. get_immutables cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_immutables_def, get_immutables_module_def, bind_def, return_def, get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_scopes[local]:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lookup_global_def, bind_def, return_def, get_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> fs[return_def, raise_def] >>
  Cases_on `FLOOKUP (get_module_globals src x).mutables n` >> fs[return_def, raise_def]
QED

Theorem set_global_scopes[local]:
  !cx src n v st res st'. set_global cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_global_def, bind_def, return_def, get_current_globals_def, set_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem set_immutable_scopes[local]:
  !cx src n v st res st'. set_immutable cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_immutable_def, bind_def, return_def, get_current_globals_def, set_current_globals_def, lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem push_log_scopes[local]:
  !l st res st'. push_log l st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[push_log_def, return_def] >> simp[]
QED

Theorem transfer_value_scopes[local]:
  !f t a st res st'. transfer_value f t a st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def, check_def, assert_def, update_accounts_def] >>
  gvs[raise_def] >> simp[]
QED

(* Scope-modifying operations *)
Theorem push_scope_len[local]:
  !st res st'. push_scope st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes + 1
Proof
  rw[push_scope_def, return_def] >> simp[]
QED

Theorem push_scope_with_var_len[local]:
  !nm v st res st'. push_scope_with_var nm v st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes + 1
Proof
  rw[push_scope_with_var_def, return_def] >> simp[]
QED

Theorem pop_scope_len[local]:
  !st res st'. pop_scope st = (res, st') /\ st.scopes <> [] ==> LENGTH st'.scopes = LENGTH st.scopes - 1
Proof
  rw[pop_scope_def] >> Cases_on `st.scopes` >> gvs[return_def]
QED

Theorem set_scopes_len[local]:
  !env st res st'. set_scopes env st = (res, st') ==> LENGTH st'.scopes = LENGTH env
Proof
  rw[set_scopes_def, return_def] >> simp[]
QED

Theorem find_containing_scope_len[local]:
  !id sc pre env v rest. find_containing_scope id sc = SOME (pre, env, v, rest) ==>
     LENGTH (pre ++ env :: rest) = LENGTH sc
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rw[] >> rpt strip_tac >> qpat_x_assum `_ = SOME _` mp_tac >>
  simp[find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >> simp[] >>
  strip_tac >> PairCases_on `z` >> fs[] >>
  first_x_assum (qspecl_then [`id`, `z0`, `z1`, `z2`, `z3`] mp_tac) >> simp[]
QED

Theorem new_variable_scopes_len[local]:
  !id v st res st'. new_variable id v st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, get_scopes_def, return_def, check_def, assert_def] >>
  Cases_on `IS_NONE (lookup_scopes (string_to_num id) st.scopes)` >> fs[raise_def] >>
  Cases_on `st.scopes` >> gvs[set_scopes_def, return_def, raise_def]
QED

Theorem set_variable_scopes_len[local]:
  !id v st res st'. set_variable id v st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes
Proof
  rw[set_variable_def, bind_def, ignore_bind_def, get_scopes_def, return_def, lift_option_def] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >> fs[raise_def] >>
  PairCases_on `x` >> fs[set_scopes_def, return_def] >> gvs[] >>
  imp_res_tac find_containing_scope_len >> fs[]
QED

Theorem push_function_scopes[local]:
  !src_fn sc cx st res st' cxf.
    push_function src_fn sc cx st = (INL cxf, st') ==> st'.scopes = [sc]
Proof
  rw[push_function_def, return_def] >> simp[]
QED

Theorem pop_function_scopes[local]:
  !prev st res st'. pop_function prev st = (res, st') ==> st'.scopes = prev
Proof
  rw[pop_function_def, set_scopes_def, return_def] >> simp[]
QED

(* Key lemma: bind preserves scopes if both f and g preserve scopes *)
Theorem bind_scopes_len[local]:
  !func g st res st'.
    monad_bind func g st = (res, st') /\
    (!st1 res1 st1'. func st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) /\
    (!x st1 res1 st1'. g x st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) ==>
    LENGTH st'.scopes = LENGTH st.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `monad_bind _ _ _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `func st` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  res_tac >> gvs[]
QED

(* Key lemma: finally with push/pop preserves length *)
Theorem finally_push_pop_len[local]:
  !body st res st'.
    finally (do push_scope; body od) pop_scope st = (res, st') /\
    (!st1 res1 st1'. body st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) ==>
    LENGTH st'.scopes = LENGTH st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def, bind_def, ignore_bind_def, push_scope_def, return_def, pop_scope_def, raise_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`st with scopes updated_by CONS FEMPTY`] mp_tac) >> simp[]
QED

Theorem finally_push_var_pop_len[local]:
  !nm v body st res st'.
    finally (do push_scope_with_var nm v; body od) pop_scope st = (res, st') /\
    (!st1 res1 st1'. body st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) ==>
    LENGTH st'.scopes = LENGTH st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def, bind_def, ignore_bind_def, push_scope_with_var_def, return_def, pop_scope_def, raise_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`st with scopes updated_by CONS (FEMPTY |+ (nm, v))`] mp_tac) >> simp[]
QED

(* Switch_BoolV preserves length if both branches preserve length *)
Theorem switch_BoolV_scopes_len[local]:
  !v f g st res st'.
    switch_BoolV v f g st = (res, st') /\
    (!st1 res1 st1'. f st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) /\
    (!st1 res1 st1'. g st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) ==>
    LENGTH st'.scopes = LENGTH st.scopes
Proof
  rw[switch_BoolV_def, raise_def] >> metis_tac[]
QED

(* assign_target preserves scopes length *)
(* Proof strategy: mutual induction on assign_target_ind, then:
   - ScopedVar: use find_containing_scope_len
   - TopLevelVar/ImmutableVar: case split on ALOOKUP, return/raise preserve state
   - TupleTargetV error cases: just simp with raise_def
   - assign_targets recursive: use IH via res_tac *)
Theorem assign_target_scopes_len[local]:
  (!cx gv ao st res st'. assign_target cx gv ao st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes) /\
  (!cx gvs vs st res st'. assign_targets cx gvs vs st = (res, st') ==> LENGTH st'.scopes = LENGTH st.scopes)
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar case *)
  >- (strip_tac >>
      gvs[assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
      Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
      PairCases_on `x` >> gvs[bind_def, lift_sum_def] >>
      Cases_on `assign_subscripts x2 (REVERSE is) ao` >>
      gvs[return_def, raise_def, bind_def, ignore_bind_def, set_scopes_def] >>
      drule find_containing_scope_len >> simp[])
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
      res_tac >> imp_res_tac get_Value_scopes >> gvs[] >> metis_tac[])
  (* assign_targets length mismatch cases *)
  >- simp[assign_target_def, raise_def]
  >- simp[assign_target_def, raise_def]
QED

(* ===== Helper lemmas for difficult cases in scopes_len_mutual ===== *)

(* Goal 13: If statement - the body is wrapped in push_scope/pop_scope via finally *)
Theorem if_stmt_scopes_len[local]:
  !cx e ss ss' st res st'.
    eval_stmt cx (If e ss ss') st = (res, st') /\
    (!st1 res1 st1'. eval_expr cx e st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) /\
    (!st1 res1 st1'. eval_stmts cx ss st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) /\
    (!st1 res1 st1'. eval_stmts cx ss' st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  cheat
QED

(* Goal 14: For statement - delegates to eval_for after check *)
Theorem for_stmt_scopes_len[local]:
  !cx id typ it n body st res st'.
    eval_stmt cx (For id typ it n body) st = (res, st') /\
    (!st1 res1 st1'. eval_iterator cx it st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) /\
    (!vs st1 res1 st1'. eval_for cx (string_to_num id) body vs st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  cheat
QED

(* Goal 28: eval_for (v::vs) - uses push_scope_with_var/pop_scope via finally *)
Theorem eval_for_cons_scopes_len[local]:
  !cx nm body v vs st res st'.
    eval_for cx nm body (v::vs) st = (res, st') /\
    (!st1 res1 st1'. eval_stmts cx body st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) /\
    (!st1 res1 st1'. eval_for cx nm body vs st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  cheat
QED

(* Goal 43: IntCall - uses push_function/pop_function via finally *)
Theorem intcall_scopes_len[local]:
  !cx src_id_opt fn es st res st'.
    eval_expr cx (Call (IntCall (src_id_opt, fn)) es) st = (res, st') /\
    (!st1 res1 st1'. eval_exprs cx es st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) /\
    (* IH for body - note: runs with different cx' but body preserves scopes *)
    (!cx' body st1 res1 st1'. eval_stmts cx' body st1 = (res1, st1') ==> LENGTH st1.scopes = LENGTH st1'.scopes) ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  cheat
QED

(* Tactic for simple cases that just expand defs and use helper lemmas *)
val simple_tac = rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  res_tac >>
  TRY (imp_res_tac get_Value_scopes) >>
  TRY (imp_res_tac lift_option_scopes) >>
  TRY (imp_res_tac lift_sum_scopes) >>
  TRY (imp_res_tac check_scopes) >>
  TRY (imp_res_tac push_log_scopes) >>
  TRY (imp_res_tac new_variable_scopes_len) >>
  TRY (imp_res_tac set_variable_scopes_len) >>
  TRY (imp_res_tac assign_target_scopes_len) >>
  TRY (imp_res_tac lookup_global_scopes) >>
  TRY (imp_res_tac transfer_value_scopes) >>
  gvs[];

(* Main mutual scopes length preservation theorem *)
Theorem scopes_len_mutual[local]:
  (!cx s st res st'. eval_stmt cx s st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx it st res st'. eval_iterator cx it st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx g st res st'. eval_target cx g st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx gs st res st'. eval_targets cx gs st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx bt st res st'. eval_base_target cx bt st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx nm body vs st res st'. eval_for cx nm body vs st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx e st res st'. eval_expr cx e st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res, st') ==> LENGTH st.scopes = LENGTH st'.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac
  (* 1. Pass *)
  >- simp[evaluate_def, return_def]
  (* 2. Continue *)
  >- simp[evaluate_def, raise_def]
  (* 3. Break *)
  >- simp[evaluate_def, raise_def]
  (* 4. Return NONE *)
  >- simp[evaluate_def, raise_def]
  (* 5. Return (SOME e) *)
  >- simple_tac
  (* 6. Raise e *)
  >- simple_tac
  (* 7. Assert *)
  >- (rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      res_tac >> gvs[switch_BoolV_def, return_def, raise_def, bind_def, AllCaseEqs()] >>
      res_tac >> imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
      Cases_on `tv = Value (BoolV T)` >> gvs[return_def] >>
      Cases_on `tv = Value (BoolV F)` >> gvs[raise_def, bind_def, AllCaseEqs()] >>
      res_tac >> imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> gvs[] >>
      metis_tac[])
  (* 8. Log *)
  >- simple_tac
  (* 9. AnnAssign *)
  >- simple_tac
  (* 10. Append *)
  >- (simple_tac >>
      PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
      gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac get_Value_scopes >> imp_res_tac assign_target_scopes_len >> gvs[] >>
      TRY (first_x_assum drule >> simp[]) >>
      TRY (first_x_assum (qspecl_then [`st`, `x0`, `x1`, `s''`] mp_tac) >> simp[]))
  (* 11. Assign *)
  >- (simple_tac >>
      gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac assign_target_scopes_len >> gvs[] >> TRY (first_x_assum drule >> simp[]))
  (* 12. AugAssign *)
  >- (rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      PairCases_on `x` >> gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac get_Value_scopes >> imp_res_tac assign_target_scopes_len >> gvs[] >>
      TRY (first_x_assum drule >> simp[]) >>
      TRY (first_x_assum (qspecl_then [`st`, `x0`, `x1`, `s''`] mp_tac) >> simp[]))
  (* 13. If - use helper lemma *)
  >- (rpt strip_tac >> irule if_stmt_scopes_len >>
      MAP_EVERY qexists_tac [`e`, `ss`, `ss'`] >> simp[] >> metis_tac[])
  (* 14. For - use helper lemma *)
  >- (rpt strip_tac >> irule for_stmt_scopes_len >>
      MAP_EVERY qexists_tac [`body`, `id`, `it`, `n`, `typ`] >> simp[] >> metis_tac[])
  (* 15. Expr *)
  >- (simple_tac >>
      gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def] >>
      imp_res_tac get_Value_scopes >> gvs[] >> res_tac >> gvs[])
  (* 16. eval_stmts [] *)
  >- simp[evaluate_def, return_def]
  (* 17. eval_stmts (s::ss) *)
  >- (simple_tac >> TRY (first_x_assum drule >> simp[]) >>
      gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
      first_x_assum drule >> simp[] >> strip_tac >> res_tac >> gvs[])
  (* 18. Array iterator *)
  >- simple_tac
  (* 19. Range iterator *)
  >- (simple_tac >>
      imp_res_tac get_Value_scopes >> gvs[] >> res_tac >> gvs[] >>
      imp_res_tac lift_sum_scopes >> gvs[] >>
      TRY (first_x_assum drule >> simp[]) >>
      TRY (first_x_assum (qspecl_then [`st`, `tv1`, `s''`, `s''`, `v`, `s''`] mp_tac) >> simp[]))
  (* 20. BaseTarget *)
  >- simple_tac
  (* 21. TupleTarget *)
  >- simple_tac
  (* 22. eval_targets [] *)
  >- simp[evaluate_def, return_def]
  (* 23. eval_targets (g::gs) *)
  >- (simple_tac >> TRY (first_x_assum drule >> simp[]))
  (* 24. NameTarget *)
  >- simp[evaluate_def, return_def]
  (* 25. TopLevelNameTarget *)
  >- (simp[evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
      imp_res_tac lookup_global_scopes >> gvs[return_def])
  (* 26. AttributeTarget *)
  >- simple_tac
  (* 27. SubscriptTarget *)
  >- (simple_tac >> imp_res_tac get_Value_scopes >> gvs[] >>
      TRY (first_x_assum drule >> simp[]) >>
      TRY (first_x_assum (qspecl_then [`st`, `x0`, `x1`, `s''`] mp_tac) >> simp[]))
  (* 28. eval_for [] *)
  >- simp[evaluate_def, return_def]
  (* 29. eval_for (v::vs) - use helper lemma *)
  >- (rpt strip_tac >> irule eval_for_cons_scopes_len >>
      MAP_EVERY qexists_tac [`body`, `v`, `vs`] >> simp[] >> metis_tac[])
  (* 30. Name *)
  >- (simp[evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[lift_option_def, return_def, raise_def])
  (* 31. TopLevelName *)
  >- (simp[evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
      imp_res_tac lookup_global_scopes >> gvs[return_def])
  (* 32. FlagMember *)
  >- simp[evaluate_def, return_def]
  (* 33. IfExp *)
  >- (rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      res_tac >> gvs[switch_BoolV_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac get_Value_scopes >> gvs[] >> res_tac >> gvs[] >>
      TRY (first_x_assum drule >> simp[]))
  (* 34. Literal *)
  >- simp[evaluate_def, return_def]
  (* 35. StructLit *)
  >- (simple_tac >> gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac lift_option_scopes >> gvs[])
  (* 36. Subscript *)
  >- (simple_tac >> imp_res_tac get_Value_scopes >> gvs[] >>
      imp_res_tac lift_option_scopes >> imp_res_tac lift_sum_scopes >> gvs[] >>
      TRY (first_x_assum drule >> simp[]))
  (* 37. Attribute *)
  >- (simple_tac >> imp_res_tac get_Value_scopes >> gvs[] >>
      imp_res_tac lift_option_scopes >> gvs[])
  (* 38. Builtin *)
  >- (simple_tac >> gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac check_scopes >> gvs[] >> imp_res_tac lift_sum_scopes >> gvs[])
  (* 39. Pop *)
  >- (simple_tac >> PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac assign_target_scopes_len >> gvs[])
  (* 40. TypeBuiltin *)
  >- (simple_tac >> gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac check_scopes >> gvs[] >> imp_res_tac lift_sum_scopes >> gvs[])
  (* 41. Send *)
  >- (simple_tac >> gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac check_scopes >> imp_res_tac get_Value_scopes >> imp_res_tac transfer_value_scopes >> gvs[])
  (* 42. ExtCall *)
  >- simp[evaluate_def, raise_def]
  (* 43. IntCall - use helper lemma *)
  >- (rpt strip_tac >> irule intcall_scopes_len >>
      MAP_EVERY qexists_tac [`es`, `fn`, `src_id_opt`] >> simp[] >> metis_tac[])
  (* 44. eval_exprs [] *)
  >- simp[evaluate_def, return_def]
  (* 45. eval_exprs (e::es) *)
  >- (simple_tac >> imp_res_tac get_Value_scopes >> gvs[] >>
      TRY (first_x_assum drule >> simp[]) >>
      TRY (first_x_assum (qspecl_then [`st`, `tv`, `s''`, `s''`, `v`, `s''`] mp_tac) >> simp[]))
QED

(* Main theorem: evaluation preserves scopes length *)
Theorem scopes_len_preserved:
  !cx ss st res st'.
    eval_stmts cx ss st = (res, st') ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  metis_tac[scopes_len_mutual]
QED
