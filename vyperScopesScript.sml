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

(* Helper for the exact pattern in If statements: do push_scope; finally body pop_scope od *)
Theorem push_scope_finally_pop_len[local]:
  !body st res st'.
    do push_scope; finally body pop_scope od st = (res, st') /\
    (!st1 res1 st1'. body st1 = (res1, st1') ==> LENGTH st1'.scopes = LENGTH st1.scopes) ==>
    LENGTH st'.scopes = LENGTH st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do _ ; _ od _ = _` mp_tac >>
  simp[vyperInterpreterTheory.bind_def, finally_def, ignore_bind_def,
       push_scope_def, pop_scope_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum (qspecl_then [`st with scopes updated_by CONS FEMPTY`] mp_tac) >> simp[])
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

(* ===== Helper lemmas ===== *)

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

(* Helper for chain reasoning through multiple states *)
val chain_tac = rpt (
  TRY (first_x_assum drule >> simp[] >> strip_tac) >>
  TRY res_tac >> gvs[] >>
  TRY (imp_res_tac get_Value_scopes >> gvs[]) >>
  TRY (imp_res_tac lift_option_scopes >> gvs[]) >>
  TRY (imp_res_tac lift_sum_scopes >> gvs[]) >>
  TRY (imp_res_tac check_scopes >> gvs[]) >>
  TRY (imp_res_tac assign_target_scopes_len >> gvs[])
  ) >> TRY (metis_tac[]);

Theorem case_Pass[local]:
  ∀cx st res st'.
    eval_stmt cx Pass st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_Continue[local]:
  ∀cx st res st'.
    eval_stmt cx Continue st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, raise_def]
QED

Theorem case_Break[local]:
  ∀cx st res st'.
    eval_stmt cx Break st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, raise_def]
QED

Theorem case_Return_NONE[local]:
  ∀cx st res st'.
    eval_stmt cx (Return NONE) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, raise_def]
QED

Theorem case_Return_SOME[local]:
  ∀cx e.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_Raise[local]:
  ∀cx e.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Raise e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_Assert[local]:
  ∀cx e e'.
    (∀s'' tv t.
       eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'.
         eval_expr cx e' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assert e e') st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def] >>
  Cases_on `tv = Value (BoolV T)` >> gvs[return_def] >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def, bind_def, AllCaseEqs()] >>
  chain_tac
QED

Theorem case_Log[local]:
  ∀cx id es.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_AnnAssign[local]:
  ∀cx id typ e.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_Append[local]:
  ∀cx bt e.
    (∀s'' loc sbs t'.
       eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'.
         eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Append bt e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_Assign[local]:
  ∀cx g e.
    (∀s'' gv t.
       eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'.
         eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_target cx g st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Assign g e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_AugAssign[local]:
  ∀cx bt bop e.
    (∀s'' loc sbs t'.
       eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'.
         eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign bt bop e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_If[local]:
  ∀cx e ss ss'.
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'.
         eval_stmts cx ss st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'.
         eval_stmts cx ss' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (If e ss ss') st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  sg `∀st1 res1 st1'. switch_BoolV tv (eval_stmts cx ss) (eval_stmts cx ss') st1 = (res1,st1') ⇒ LENGTH st1'.scopes = LENGTH st1.scopes`
  >- (rpt strip_tac >> imp_res_tac switch_BoolV_scopes_len >>
      qpat_x_assum `(_ ==> _ ==> _)` irule >>
      conj_tac >> rpt strip_tac >> ntac 2 (last_x_assum (qspecl_then [`st`, `tv`, `s''`] mp_tac)) >>
      simp[push_scope_def, return_def] >> rpt strip_tac >> res_tac >> simp[]) >>
  imp_res_tac push_scope_finally_pop_len >> gvs[]
QED

Theorem case_For[local]:
  ∀cx id typ it n body.
    (∀s'' vs t s'³' x t'.
       eval_iterator cx it s'' = (INL vs,t) ∧
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'³' = (INL x,t') ⇒
       ∀st res st'.
         eval_for cx (string_to_num id) body vs st = (res,st') ⇒
         LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_iterator cx it st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  fs[evaluate_def, bind_def] >>
  Cases_on `eval_iterator cx it st` >> rename1 `eval_iterator cx it st = iter_result` >>
  Cases_on `iter_result` >> rename1 `_ = (iter_res_val, st_after_iter)` >>
  fs[] >>
  Cases_on `iter_res_val` >> fs[] >>
  rename1 `INL values_list` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH values_list)` >>
  fs[check_def, assert_def, return_def, raise_def, bind_def] >>
  gvs[]
  (* Subgoal 1: compatible_bound is TRUE - use helper *)
  >- (gvs[ignore_bind_def, assert_def, bind_def, return_def] >>
      last_x_assum (qspecl_then [`st`, `INL values_list`, `st_after_iter`] mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`st`, `values_list`, `st_after_iter`] mp_tac) >>
      simp[])
  (* Subgoal 2: compatible_bound is FALSE - assert fails, use iterator IH directly *)
  >> gvs[ignore_bind_def, assert_def, bind_def, return_def, raise_def] >>
     res_tac >> simp[]
QED

Theorem case_Expr[local]:
  ∀cx e.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_Value_scopes >> gvs[] >> res_tac >> gvs[]
QED

Theorem case_eval_stmts_nil[local]:
  ∀cx st res st'.
    eval_stmts cx [] st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_stmts_cons[local]:
  ∀cx s ss.
    (∀s'' x t.
       eval_stmt cx s s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_stmts cx ss st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_stmt cx s st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac >> TRY (first_x_assum drule >> simp[]) >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[] >> strip_tac >> res_tac >> gvs[]
QED

Theorem case_Array_iterator[local]:
  ∀cx e.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_Range_iterator[local]:
  ∀cx e e'.
    (∀s'' tv1 t s'³' s t'.
       eval_expr cx e s'' = (INL tv1,t) ∧ get_Value tv1 s'³' = (INL s,t') ⇒
       ∀st res st'.
         eval_expr cx e' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_iterator cx (Range e e') st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_BaseTarget[local]:
  ∀cx bt.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  rpt strip_tac >> gvs[return_def] >> res_tac >> simp[] >>
  PairCases_on `x` >> gvs[return_def]
QED

Theorem case_TupleTarget[local]:
  ∀cx gs.
    (∀st res st'.
       eval_targets cx gs st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_target cx (TupleTarget gs) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac
QED

Theorem case_eval_targets_nil[local]:
  ∀cx st res st'.
    eval_targets cx [] st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_targets_cons[local]:
  ∀cx g gs.
    (∀s'' gv t.
       eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'.
         eval_targets cx gs st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_target cx g st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_NameTarget[local]:
  ∀cx id st res st'.
    eval_base_target cx (NameTarget id) st = (res,st') ⇒
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, get_scopes_def, return_def, AllCaseEqs()] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def, bind_def, AllCaseEqs()] >>
  imp_res_tac get_immutables_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

Theorem case_TopLevelNameTarget[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt,id)) st = (res,st') ⇒
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac lookup_global_scopes >> gvs[return_def]
QED

Theorem case_AttributeTarget[local]:
  ∀cx bt id.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget bt id) st = (res,st') ⇒
      LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  rpt strip_tac >> gvs[return_def] >> res_tac >> simp[] >>
  PairCases_on `x` >> gvs[return_def]
QED

Theorem case_SubscriptTarget[local]:
  ∀cx bt e.
    (∀s'' loc sbs t'.
       eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'.
         eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget bt e) st = (res,st') ⇒
      LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_eval_for_nil[local]:
  ∀cx nm body st res st'.
    eval_for cx nm body [] st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_for_cons[local]:
  ∀cx nm body v vs.
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm v s'' = (INL x,t) ∧
       finally
         (try do eval_stmts cx body; return F od handle_loop_exception)
         pop_scope s'³' = (INL broke,t') ∧ ¬broke ⇒
       ∀st res st'.
         eval_for cx nm body vs st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀s'' x t.
       push_scope_with_var nm v s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_stmts cx body st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_for cx nm body (v::vs) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- ((* push succeeded, finally succeeded with some broke *)
    imp_res_tac push_scope_with_var_len >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), try_def] >>
    strip_tac >> gvs[bind_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def]
    >- ((* body succeeded with INL () *)
      first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`s''`, `INL ()`, `s'⁴'`] mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `pop_scope _ = _` mp_tac >>
      simp[pop_scope_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`st`, `s''`, `s''`, `s'⁴' with scopes := tl`] mp_tac) >>
      simp[finally_def, try_def, bind_def, AllCaseEqs(), ignore_bind_def, return_def, pop_scope_def] >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`s'⁴' with scopes := tl`, `res`, `st'`] mp_tac) >> simp[])
    >- ((* body raised exception, handled by handle_loop_exception *)
      first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`s''`, `INR e`, `s'⁵'`] mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `handle_loop_exception _ _ = _` mp_tac >>
      simp[handle_loop_exception_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      Cases_on `e = ContinueException` >> gvs[return_def, raise_def]
      >- ((* ContinueException - broke=F, recursive call *)
        qpat_x_assum `pop_scope _ = _` mp_tac >>
        simp[pop_scope_def, AllCaseEqs(), return_def] >> strip_tac >> gvs[raise_def] >>
        first_x_assum (qspecl_then [`st`, `s''`, `s''`, `s'⁴' with scopes := tl`] mp_tac) >>
        simp[finally_def, try_def, bind_def, AllCaseEqs(), ignore_bind_def, return_def,
             pop_scope_def, handle_loop_exception_def] >>
        strip_tac >>
        first_x_assum (qspecl_then [`s'⁴' with scopes := tl`, `res`, `st'`] mp_tac) >> simp[])
      >- ((* BreakException - broke=T, return () *)
        Cases_on `e = BreakException` >> gvs[return_def, raise_def] >>
        qpat_x_assum `pop_scope _ = _` mp_tac >>
        simp[pop_scope_def, AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[])))
  >- ((* push succeeded, finally returned error *)
    imp_res_tac push_scope_with_var_len >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, try_def, bind_def, AllCaseEqs(), ignore_bind_def, return_def,
         raise_def, handle_loop_exception_def, pop_scope_def] >>
    strip_tac >> gvs[]
    >- (first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`s''`, `INL ()`, `s'³'`] mp_tac) >> gvs[])
    >- (first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`s''`, `INR e'`, `s'⁵'`] mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> rw[return_def, raise_def] >> gvs[])
    >- (first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`s''`, `INR e'`, `s'⁵'`] mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> rw[return_def, raise_def] >> gvs[])
    >- (first_x_assum (qspecl_then [`st`, `s''`] mp_tac) >> simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`s''`, `INR e'`, `s'⁵'`] mp_tac) >> simp[] >> strip_tac >>
        qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> rw[return_def, raise_def] >> gvs[]))
  >- ((* push_scope_with_var failed *)
    gvs[push_scope_with_var_def, return_def])
QED

Theorem case_Name[local]:
  ∀cx id st res st'.
    eval_expr cx (Name id) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, get_scopes_def, return_def, AllCaseEqs()] >>
  imp_res_tac get_immutables_scopes >> imp_res_tac lift_sum_scopes >> gvs[]
QED

Theorem case_TopLevelName[local]:
  ∀cx src_id_opt id st res st'.
    eval_expr cx (TopLevelName (src_id_opt,id)) st = (res,st') ⇒
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac lookup_global_scopes >> gvs[return_def]
QED

Theorem case_FlagMember[local]:
  ∀cx nsid mid st res st'.
    eval_expr cx (FlagMember nsid mid) st = (res,st') ⇒
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[evaluate_def, lookup_flag_mem_def, raise_def, return_def] >>
  rpt CASE_TAC >> simp[raise_def, return_def]
QED

Theorem case_IfExp[local]:
  ∀cx e e' e''.
    (∀s'' tv t.
       eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'.
         eval_expr cx e' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀s'' tv t.
       eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'.
         eval_expr cx e'' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (IfExp e e' e'') st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def] >>
  Cases_on `tv = Value (BoolV T)` >> gvs[] >>
  Cases_on `tv = Value (BoolV F)` >> gvs[raise_def] >>
  res_tac >> gvs[] >> metis_tac[]
QED

Theorem case_Literal[local]:
  ∀cx l st res st'.
    eval_expr cx (Literal l) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_StructLit[local]:
  ∀cx src_id_opt id kes.
    (∀ks.
       ks = MAP FST kes ⇒
       ∀st res st'.
         eval_exprs cx (MAP SND kes) st = (res,st') ⇒
         LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (StructLit (src_id_opt,id) kes) st = (res,st') ⇒
      LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac >> gvs[ignore_bind_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac lift_option_scopes >> gvs[]
QED

Theorem case_Subscript[local]:
  ∀cx e e'.
    (∀s'' tv1 t.
       eval_expr cx e s'' = (INL tv1,t) ⇒
       ∀st res st'.
         eval_expr cx e' st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Subscript e e') st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  chain_tac
QED

Theorem case_Attribute[local]:
  ∀cx e id.
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Attribute e id) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simple_tac >> imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> gvs[]
QED

Theorem case_Builtin[local]:
  ∀cx bt es.
    (∀s'' x t.
       check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Builtin bt es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def] >>
  imp_res_tac check_scopes >> gvs[] >>
  imp_res_tac get_accounts_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> gvs[] >>
  res_tac >> gvs[]
QED

Theorem case_Pop[local]:
  ∀cx bt.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Pop bt) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac assign_target_scopes_len >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  res_tac >> gvs[]
QED

Theorem case_TypeBuiltin[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin tb typ es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def] >>
  TRY (imp_res_tac check_scopes >> gvs[]) >>
  TRY (imp_res_tac lift_sum_scopes >> gvs[]) >>
  TRY (res_tac >> gvs[])
QED

Theorem case_Send[local]:
  ∀cx es.
    (∀s'' x t.
       check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call Send es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def] >>
  TRY (imp_res_tac check_scopes >> gvs[]) >>
  TRY (imp_res_tac lift_option_scopes >> gvs[]) >>
  TRY (imp_res_tac transfer_value_scopes >> gvs[]) >>
  TRY (res_tac >> gvs[])
QED

Theorem case_ExtCall[local]:
  ∀cx cx' vs st res st'.
    eval_expr cx (Call (ExtCall cx') vs) st = (res,st') ⇒
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, raise_def]
QED

(* Helper: finally with set_scopes restores scopes to the given value *)
Theorem finally_set_scopes[local]:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ s'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[] >> gvs[]
QED

Theorem case_IntCall[local]:
  ∀cx src_id_opt fn es.
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup ret ss s'⁵' x' t'³'
         s'⁶' vs t'⁴' tenv s'⁷' env t'⁵' s'⁸' prev t'⁶' s'⁹' rtv t'⁷' s'¹⁰'
         cx' t'⁸'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_function fn Internal ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ ret = FST sstup ∧
       ss = SND sstup ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'⁵' = (INL x',t'³') ∧
       eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
       tenv = type_env ts ∧
       lift_option (bind_arguments tenv args vs) "IntCall bind_arguments"
         s'⁷' = (INL env,t'⁵') ∧ get_scopes s'⁸' = (INL prev,t'⁶') ∧
       lift_option (evaluate_type tenv ret) "IntCall eval ret" s'⁹' = (INL rtv,t'⁷') ∧
       push_function (src_id_opt,fn) env cx s'¹⁰' = (INL cx',t'⁸') ⇒
       ∀st res st'.
         eval_stmts cx' ss st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀s'' x t s'³' ts t' s'⁴' tup t'' stup args sstup ret body' s'⁵' x' t'³'.
       check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
       lift_option (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'³' = (INL ts,t') ∧
       lift_option (lookup_function fn Internal ts)
         "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ stup = SND tup ∧
       args = FST stup ∧ sstup = SND stup ∧ ret = FST sstup ∧
       body' = SND sstup ∧
       check (LENGTH args = LENGTH es) "IntCall args length" s'⁵' = (INL x',t'³') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call (IntCall (src_id_opt,fn)) es) st = (res,st') ⇒
      LENGTH st.scopes = LENGTH st'.scopes
Proof
  let
    val opt_tac = fn qtm =>
      Cases_on qtm >> gvs[return_def, raise_def]
    val sub_tac =
      TRY (opt_tac `get_module_code cx src_id_opt`) >>
      TRY (opt_tac `lookup_function fn Internal ts`) >>
      TRY (opt_tac `bind_arguments (type_env ts) (FST (SND tup)) vs`) >>
      TRY (opt_tac `evaluate_type (type_env ts) (FST (SND (SND tup)))`) >>
      TRY (opt_tac `safe_cast rtv rv`) >>
      TRY (drule_all finally_set_scopes >> strip_tac >> gvs[]) >>
      TRY (last_x_assum mp_tac >> simp[check_def, assert_def, return_def, lift_option_def])
  in
    rpt strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
         check_def, assert_def, lift_option_def, get_scopes_def, push_function_def,
         pop_function_def, set_scopes_def] >>
    strip_tac >> gvs[return_def, raise_def] >>
    sub_tac >> sub_tac >> sub_tac >> sub_tac >> sub_tac >>
    sub_tac >> sub_tac >> sub_tac >> sub_tac
  end
QED

Theorem case_eval_exprs_nil[local]:
  ∀cx st res st'.
    eval_exprs cx [] st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

Theorem case_eval_exprs_cons[local]:
  ∀cx e es.
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ get_Value tv s'³' = (INL v,t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes) ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res,st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  res_tac >> gvs[] >>
  first_x_assum (drule_then assume_tac) >> gvs[]
QED

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
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  (* 1. Pass *)
  >- ACCEPT_TAC case_Pass
  (* 2. Continue *)
  >- ACCEPT_TAC case_Continue
  (* 3. Break *)
  >- ACCEPT_TAC case_Break
  (* 4. Return NONE *)
  >- ACCEPT_TAC case_Return_NONE
  (* 5. Return (SOME e) *)
  >- ACCEPT_TAC case_Return_SOME
  (* 6. Raise e *)
  >- ACCEPT_TAC case_Raise
  (* 7. Assert *)
  >- ACCEPT_TAC case_Assert
  (* 8. Log *)
  >- ACCEPT_TAC case_Log
  (* 9. AnnAssign *)
  >- ACCEPT_TAC case_AnnAssign
  (* 10. Append *)
  >- ACCEPT_TAC case_Append
  (* 11. Assign *)
  >- ACCEPT_TAC case_Assign
  (* 12. AugAssign *)
  >- ACCEPT_TAC case_AugAssign
  (* 13. If - complex proof, see if_stmt_scopes_len *)
  >- ACCEPT_TAC case_If
  (* 14. For - complex proof, see for_stmt_scopes_len *)
  >- ACCEPT_TAC case_For
  (* 15. Expr *)
  >- ACCEPT_TAC case_Expr
  (* 16. eval_stmts [] *)
  >- ACCEPT_TAC case_eval_stmts_nil
  (* 17. eval_stmts (s::ss) *)
  >- ACCEPT_TAC case_eval_stmts_cons
  (* 18. Array iterator *)
  >- ACCEPT_TAC case_Array_iterator
  (* 19. Range iterator *)
  >- ACCEPT_TAC case_Range_iterator
  (* 20. BaseTarget *)
  >- ACCEPT_TAC case_BaseTarget
  (* 21. TupleTarget *)
  >- ACCEPT_TAC case_TupleTarget
  (* 22. eval_targets [] *)
  >- ACCEPT_TAC case_eval_targets_nil
  (* 23. eval_targets (g::gs) *)
  >- ACCEPT_TAC case_eval_targets_cons
  (* 24. NameTarget *)
  >- ACCEPT_TAC case_NameTarget
  (* 25. TopLevelNameTarget *)
  >- ACCEPT_TAC case_TopLevelNameTarget
  (* 26. AttributeTarget *)
  >- ACCEPT_TAC case_AttributeTarget
  (* 27. SubscriptTarget *)
  >- ACCEPT_TAC case_SubscriptTarget
  (* 28. eval_for [] *)
  >- ACCEPT_TAC case_eval_for_nil
  (* 29. eval_for (v::vs) - complex proof, see eval_for_cons_scopes_len *)
  >- ACCEPT_TAC case_eval_for_cons
  (* 30. Name *)
  >- ACCEPT_TAC case_Name
  (* 31. TopLevelName *)
  >- ACCEPT_TAC case_TopLevelName
  (* 32. FlagMember *)
  >- ACCEPT_TAC case_FlagMember
  (* 33. IfExp *)
  >- ACCEPT_TAC case_IfExp
  (* 34. Literal *)
  >- ACCEPT_TAC case_Literal
  (* 35. StructLit *)
  >- ACCEPT_TAC case_StructLit
  (* 36. Subscript *)
  >- ACCEPT_TAC case_Subscript
  (* 37. Attribute *)
  >- ACCEPT_TAC case_Attribute
  (* 38. Builtin *)
  >- ACCEPT_TAC case_Builtin
  (* 39. Pop *)
  >- ACCEPT_TAC case_Pop
  (* 40. TypeBuiltin *)
  >- ACCEPT_TAC case_TypeBuiltin
  (* 41. Send *)
  >- ACCEPT_TAC case_Send
  (* 42. ExtCall *)
  >- ACCEPT_TAC case_ExtCall
  (* 43. IntCall - complex proof, see intcall_scopes_len *)
  >- ACCEPT_TAC case_IntCall
  (* 44. eval_exprs [] *)
  >- ACCEPT_TAC case_eval_exprs_nil
  (* 45. eval_exprs (e::es) *)
  >- ACCEPT_TAC case_eval_exprs_cons
QED

(* Main theorem: evaluation preserves scopes length *)
Theorem scopes_len_preserved:
  !cx ss st res st'.
    eval_stmts cx ss st = (res, st') ==>
    LENGTH st.scopes = LENGTH st'.scopes
Proof
  metis_tac[scopes_len_mutual]
QED
