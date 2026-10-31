Theory vyperLogPreservation

Ancestors
  pair option sum vyperMisc vyperCall vyperStatePreservation vyperCallFrame vyperCallOutcomeFrame
  vyperState[ignore_grammar] vyperInterpreter[ignore_grammar] vyperCallOutcome[ignore_grammar] vyperCallOutcomeProps[ignore_grammar]
  vyperCreate vyperCreateFrame vyperPlaceFrames vyperAbiFrame vyperAbiMemoryProps
  vyperScopePreservation

(* Keep existing free statement-list variables when importing oracle grammar. *)
val _ = hide "body";

Definition log_extends_def:
  log_extends (st:evaluation_state) (st':evaluation_state) <=>
    isPREFIX st.logs st'.logs
End

Theorem log_extends_refl:
  log_extends st st
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_trans:
  log_extends st st1 /\ log_extends st1 st2 ==> log_extends st st2
Proof
  simp[log_extends_def] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem log_extends_eq_logs:
  st.logs = st'.logs ==> log_extends st st'
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_append:
  log_extends st (st with logs := st.logs ++ events)
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem return_log_extends[local]:
  return x st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.return_def, log_extends_refl]
QED

Theorem raise_log_extends[local]:
  raise e st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.raise_def, log_extends_refl]
QED

Theorem push_log_log_extends[local]:
  push_log ev st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[push_log_logs] >> simp[log_extends_append]
QED

Theorem append_logs_log_extends[local]:
  append_logs events st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[append_logs_logs] >> simp[log_extends_append]
QED

Theorem bind_log_extends[local]:
  (!r st1. f st = (r,st1) ==> log_extends st st1) /\
  (!x st1 r st2.
     f st = (INL x,st1) /\ g x st1 = (r,st2) ==>
     log_extends st1 st2) /\
  bind f g st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >>
  gvs[vyperStateTheory.bind_def] >>
  Cases_on `q` >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem bind_log_extends_forward[local]:
  bind f g st = (res,st') ==>
  (!r st1. f st = (r,st1) ==> log_extends st st1) ==>
  (!x st1 r st2.
     f st = (INL x,st1) /\ g x st1 = (r,st2) ==>
     log_extends st1 st2) ==>
  log_extends st st'
Proof
  metis_tac[bind_log_extends]
QED

Theorem type_check_guard_specialize[local]:
  type_check p msg st = (INL (),st1) ==>
  (!s0 s1. type_check p msg s0 = (INL (),s1) ==> P) ==>
  P
Proof
  metis_tac[]
QED

Theorem equality_guard_specialize[local]:
  (!x. x = a ==> P) ==> P
Proof
  metis_tac[]
QED

Theorem case_eval_stmts_nil_logs[local]:
  eval_stmts cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_eval_stmts_cons_logs[local]:
  (!s0 x s1. eval_stmt cx s s0 = (INL x,s1) ==>
     !s2 r s3. eval_stmts cx ss s2 = (r,s3) ==> log_extends s2 s3) /\
  (!s0 r s1. eval_stmt cx s s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmts cx (s::ss) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem case_iterator_array_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_iterator cx (Array e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs(), log_extends_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `log_extends _ _` mp_tac >>
  simp[log_extends_def]
QED

Theorem case_iterator_range_logs[local]:
  (!s0 tv s1 s2 v s3.
     eval_expr cx e1 s0 = (INL tv,s1) /\
     read_result cx tv s2 = (INL v,s3) ==>
     !st res st'. eval_expr cx e2 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_iterator cx (Range e1 e2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem case_eval_for_nil_logs[local]:
  eval_for cx tyv nm body [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
       log_extends_refl]
QED

Theorem push_scope_with_var_log_extends[local]:
  push_scope_with_var nm ty v st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.push_scope_with_var_def, vyperStateTheory.return_def] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem pop_scope_log_extends[local]:
  pop_scope st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.pop_scope_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem try_body_log_extends[local]:
  (!s0 x s1. push_scope_with_var nm tyv v s0 = (INL x,s1) ==>
     !st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') /\
  push_scope_with_var nm tyv v st0 = (INL (),st1) /\
  (try (do eval_stmts cx body; return F od) handle_loop_exception) st1 =
    (res1,st1') ==>
  log_extends st1 st1'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac handle_loop_exception_state >> gvs[]
QED

Theorem finally_pop_scope_log_extends[local]:
  (!r s1. f st = (r,s1) ==> log_extends st s1) /\
  finally f pop_scope st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum ACCEPT_TAC
QED

Theorem finally_try_body_log_extends[local]:
  !cx body st1 res1 st1'.
    finally (try (do x <- eval_stmts cx body; return F od) handle_loop_exception)
            pop_scope st1 = (res1,st1') ==>
    (!st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') ==>
    log_extends st1 st1'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.try_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac handle_loop_exception_state >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  irule log_extends_trans >>
  qexists_tac `s''` >> simp[]
QED

Theorem case_eval_for_cons_logs[local]:
  (!s0 x s1 s2 broke s3.
     push_scope_with_var nm tyv v s0 = (INL x,s1) /\
     finally (try (do eval_stmts cx body; return F od)
                    handle_loop_exception) pop_scope s2 = (INL broke,s3) /\
     ~broke ==>
     !st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
       log_extends st st') /\
  (!s0 x s1. push_scope_with_var nm tyv v s0 = (INL x,s1) ==>
     !st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') ==>
  !st res st'. eval_for cx tyv nm body (v::vs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac push_scope_with_var_log_extends >>
  `!sb rb sb'. eval_stmts cx body sb = (rb,sb') ==>
               log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 s1. push_scope_with_var _ _ _ s0 = _ ==> _`
       (qspecl_then [`st`, `s''`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `log_extends s'' s'³'` by
    (drule finally_try_body_log_extends >>
     disch_then drule >> simp[]) >>
  `log_extends st s'³'` by
    (irule log_extends_trans >> qexists_tac `s''` >> simp[]) >>
  Cases_on `broke` >> gvs[vyperStateTheory.return_def] >>
  qpat_x_assum `!s0 s1 s2 s3. _`
    (qspecl_then [`st`, `s''`, `s''`, `s'³'`] mp_tac) >>
  simp[vyperStateTheory.ignore_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> qexists_tac `s'³'` >> simp[]
QED

Theorem update_accounts_logs[local]:
  update_accounts f st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.update_accounts_def, vyperStateTheory.return_def]
QED

Theorem update_transient_logs[local]:
  update_transient f st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.update_transient_def, vyperStateTheory.return_def]
QED

Theorem set_scopes_logs[local]:
  set_scopes env st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def]
QED

Theorem set_address_immutables_logs[local]:
  set_address_immutables cx imms st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_address_immutables_def,
      vyperStateTheory.return_def]
QED

Theorem set_storage_backend_logs[local]:
  set_storage_backend cx is_transient storage st = (res,st') ==>
    st'.logs = st.logs
Proof
  Cases_on `is_transient` >> rpt strip_tac >>
  gvs[vyperStateTheory.set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.update_transient_def,
      vyperStateTheory.update_accounts_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.return_def,
      AllCaseEqs()]
QED

Theorem write_storage_slot_logs[local]:
  write_storage_slot cx is_transient slot tv v st = (res,st') ==>
    st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.write_storage_slot_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac set_storage_backend_logs >> gvs[]
QED

Theorem set_immutable_logs[local]:
  set_immutable cx src n tv v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.set_immutable_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_address_immutables_state >> gvs[] >>
  imp_res_tac set_address_immutables_logs >> gvs[]
QED
Theorem set_global_logs[local]:
  set_global cx src n v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `set_global _ _ _ _ _ = _` mp_tac >>
  simp[Once vyperStateTheory.set_global_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  Cases_on `find_var_decl_by_name n ts` >>
  gvs[vyperStateTheory.raise_def] >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> gvs[]
QED

Theorem append_place_logs[local]:
  append_place cx p v st = (res,st') ==> st'.logs = st.logs
Proof
  Cases_on `p` >- (
    rename1 `StoragePlace tr slot tv` >>
    Cases_on `tv` >> simp[vyperStateTheory.append_place_def] >>
    TRY (rename1 `ArrayTV et bound` >> Cases_on `bound`) >>
    simp[vyperStateTheory.append_place_def] >>
    gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
        vyperStateTheory.check_def, vyperStateTheory.assert_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def,
        AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
    imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
    imp_res_tac lift_sum_state >> imp_res_tac write_place_logs >>
    imp_res_tac write_storage_slot_logs >> gvs[]) >>
  simp[vyperStateTheory.append_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       UNCURRY, sum_CASE_rator, prod_CASE_rator,
       AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac type_check_state >> imp_res_tac get_immutables_state >>
  imp_res_tac set_scopes_logs >> imp_res_tac set_immutable_logs >>
  imp_res_tac write_abi_memory_child_frame >>
  imp_res_tac write_abi_immutables_frame >> gvs[]
QED

Theorem pop_place_logs[local]:
  pop_place cx p st = (res,st') ==> st'.logs = st.logs
Proof
  Cases_on `p` >- (
    rename1 `StoragePlace tr slot tv` >>
    Cases_on `tv` >> simp[vyperStateTheory.pop_place_def] >>
    TRY (rename1 `ArrayTV et bound` >> Cases_on `bound`) >>
    simp[vyperStateTheory.pop_place_def, vyperStateTheory.bind_def,
         vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
         vyperStateTheory.assert_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, AllCaseEqs()] >> rpt strip_tac >>
    imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
    imp_res_tac write_storage_slot_logs >> gvs[]) >>
  simp[vyperStateTheory.pop_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.type_check_def, vyperStateTheory.check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, UNCURRY, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
  imp_res_tac get_immutables_state >>
  imp_res_tac set_scopes_logs >> imp_res_tac set_immutable_logs >>
  imp_res_tac write_abi_memory_child_frame >>
  imp_res_tac write_abi_immutables_frame >> gvs[]
QED

Theorem case_expr_subscript_logs[local]:
  (!s0 tv1 s1. eval_expr cx e1 s0 = (INL tv1,s1) ==>
     !s2 r s3. eval_expr cx e2 s2 = (r,s3) ==> log_extends s2 s3) /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'.
    eval_expr cx (Subscript ty e1 e2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  strip_tac >>
  drule bind_log_extends_forward >>
  disch_then irule >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!s0 tv1 s1. eval_expr _ e1 s0 = (INL tv1,s1) ==> _` drule >>
  strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac select_result_state >> gvs[log_extends_refl]
QED
Theorem new_variable_logs[local]:
  new_variable id tv v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.new_variable_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `st.scopes` >>
  gvs[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

(* Legacy eager-target log proofs, superseded by place frames.
Theorem storage_assignment_tail_logs[local]:
  (do current_val <- read_storage_slot cx tr slot tv;
      new_val <- lift_sum (assign_subscripts tv current_val subs ao);
      write_storage_slot cx tr slot tv new_val;
      assign_result tv ao current_val subs
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_state >> imp_res_tac lift_sum_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >>
  imp_res_tac assign_result_state >> gvs[]
QED


Theorem array_pop_tail_logs[local]:
  (do storage <- get_storage_backend cx is_transient;
      stored_len <<- w2n (lookup_storage elem_slot storage);
      check (stored_len > 0) "pop empty storage array";
      last_idx <<- stored_len - 1;
      last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
      popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
      write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
        (IntV &last_idx);
      return (SOME popped)
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem array_append_tail_logs[local]:
  (do storage <- get_storage_backend cx is_transient;
      stored_len <<- w2n (lookup_storage elem_slot storage);
      check (stored_len < n) "append full storage array";
      new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
      write_storage_slot cx is_transient new_slot app_elem_tv v;
      write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
        (IntV &(stored_len + 1));
      return NONE
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac write_storage_slot_logs >>
  imp_res_tac return_state >> gvs[]
QED

Theorem arrayref_assignment_suffix_logs[local]:
  (do (elem_slot,final_tv,remaining_subs) <-
        resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) subs;
      case (ao,final_tv) of
        (PopOp,ArrayTV pop_elem_tv (Dynamic n)) => do
          storage <- get_storage_backend cx is_transient;
          stored_len <<- w2n (lookup_storage elem_slot storage);
          check (stored_len > 0) "pop empty storage array";
          last_idx <<- stored_len - 1;
          last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
          popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
          write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
            (IntV &last_idx);
          return (SOME popped)
        od
      | (AppendOp v,ArrayTV app_elem_tv (Dynamic n)) => do
          storage <- get_storage_backend cx is_transient;
          stored_len <<- w2n (lookup_storage elem_slot storage);
          check (stored_len < n) "append full storage array";
          new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
          write_storage_slot cx is_transient new_slot app_elem_tv v;
          write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
            (IntV &(stored_len + 1));
          return NONE
        od
      | _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  once_rewrite_tac [vyperStateTheory.bind_def] >>
  qabbrev_tac `rr = resolve_array_element cx is_transient base_slot
                    (ArrayTV elem_tv bd) subs st` >>
  PairCases_on `rr` >> Cases_on `rr0` >>
  qpat_x_assum `Abbrev _` mp_tac >>
  simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `(_,_) = resolve_array_element _ _ _ _ _ _`
    (assume_tac o SYM) >>
  imp_res_tac resolve_array_element_state >> gvs[] >>
  Cases_on `final_tv` >> gvs[] >>
  TRY (Cases_on `b` >> gvs[]) >>
  Cases_on `ao` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac storage_assignment_tail_logs >>
  imp_res_tac array_pop_tail_logs >>
  imp_res_tac array_append_tail_logs >>
  pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem arrayref_assignment_normal_logs[local]:
  (do (elem_slot,final_tv,remaining_subs) <-
        resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) subs;
      case final_tv of
        BaseTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | TupleTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | ArrayTV pop_elem_tv (Fixed _) => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | ArrayTV pop_elem_tv (Dynamic n) =>
          (case ao of
             Replace _ => do
               current_val <- read_storage_slot cx is_transient elem_slot final_tv;
               new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
               write_storage_slot cx is_transient elem_slot final_tv new_val;
               assign_result final_tv ao current_val remaining_subs
             od
           | Update _ _ _ => do
               current_val <- read_storage_slot cx is_transient elem_slot final_tv;
               new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
               write_storage_slot cx is_transient elem_slot final_tv new_val;
               assign_result final_tv ao current_val remaining_subs
             od
           | AppendOp v => do
               storage <- get_storage_backend cx is_transient;
               check (w2n (lookup_storage elem_slot storage) < n)
                 "append full storage array";
               write_storage_slot cx is_transient
                 (elem_slot + n2w (type_slot_size pop_elem_tv *
                                    w2n (lookup_storage elem_slot storage) + 1))
                 pop_elem_tv v;
               write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
                 (IntV (&(w2n (lookup_storage elem_slot storage) + 1)));
               return NONE
             od
           | PopOp => do
               storage <- get_storage_backend cx is_transient;
               check (w2n (lookup_storage elem_slot storage) > 0)
                 "pop empty storage array";
               popped <- read_storage_slot cx is_transient
                 (elem_slot + n2w (type_slot_size pop_elem_tv *
                                    (w2n (lookup_storage elem_slot storage) - 1) + 1))
                 pop_elem_tv;
               write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
                 (IntV (&(w2n (lookup_storage elem_slot storage) - 1)));
               return (SOME popped)
             od)
      | StructTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | FlagTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | NoneTV => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  once_rewrite_tac [vyperStateTheory.bind_def] >>
  qabbrev_tac `rr = resolve_array_element cx is_transient base_slot
                    (ArrayTV elem_tv bd) subs st` >>
  PairCases_on `rr` >> Cases_on `rr0` >>
  qpat_x_assum `Abbrev _` mp_tac >>
  simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `(_,_) = resolve_array_element _ _ _ _ _ _`
    (assume_tac o SYM) >>
  imp_res_tac resolve_array_element_state >> gvs[] >>
  Cases_on `final_tv` >> gvs[] >>
  TRY (Cases_on `b` >> gvs[]) >>
  Cases_on `ao` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac storage_assignment_tail_logs >>
  imp_res_tac array_pop_tail_logs >>
  imp_res_tac array_append_tail_logs >>
  pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem assign_target_toplevel_logs[local]:
  assign_target cx (BaseTargetV (TopLevelVar src id) subs) ao st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  Cases_on `lookup_global cx src id st` >>
  Cases_on `q` >>
  imp_res_tac lookup_global_state >>
  pop_assum SUBST_ALL_TAC
  >- (Cases_on `x`
      >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
          simp[Once vyperStateTheory.assign_target_def,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, pairTheory.PAIR, AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
          imp_res_tac set_global_logs >> imp_res_tac assign_result_state >> gvs[])
      >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
          simp[Once vyperStateTheory.assign_target_def,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, pairTheory.PAIR, AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          rpt (pairarg_tac >> gvs[]) >>
          pop_assum mp_tac >>
          simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
          pop_assum mp_tac >>
          simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lift_option_type_state >>
          imp_res_tac read_storage_slot_state >> imp_res_tac lift_sum_state >>
          imp_res_tac write_storage_slot_logs >>
          imp_res_tac assign_result_state >> gvs[])
      >> (Cases_on `lift_option_type (get_module_code cx src)
                       "assign_target get_module_code" st` >>
          Cases_on `q` >>
          imp_res_tac lift_option_type_state >>
          pop_assum SUBST_ALL_TAC
          >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
              simp[Once vyperStateTheory.assign_target_def,
                   LET_THM, pairTheory.PAIR] >>
              strip_tac >>
              pop_assum mp_tac >>
              once_rewrite_tac [vyperStateTheory.bind_def] >>
              strip_tac >>
              gvs[Once vyperStateTheory.bind_def] >>
              drule arrayref_assignment_normal_logs >>
              simp[])
          >> (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
              simp[Once vyperStateTheory.assign_target_def,
                   vyperStateTheory.bind_def, vyperStateTheory.return_def,
                   vyperStateTheory.raise_def, LET_THM, pairTheory.PAIR] >>
              strip_tac >> gvs[])))
  >> (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, LET_THM, pairTheory.PAIR] >>
      strip_tac >> gvs[])
QED

Theorem assign_target_logs_mutual[local]:
  (!cx gv ao st res st'.
     assign_target cx gv ao st = (res,st') ==> st'.logs = st.logs) /\
  (!cx gvs vs st res st'.
     assign_targets cx gvs vs st = (res,st') ==> st'.logs = st.logs)
Proof
  ho_match_mp_tac vyperStateTheory.assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar *)
  >- (rpt strip_tac >>
      gvs[vyperStateTheory.assign_target_def, vyperStateTheory.bind_def,
          vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
          vyperStateTheory.lift_option_def] >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      PairCases_on `x` >>
      Cases_on `assign_subscripts x2.type x2.value (REVERSE is) ao` >>
      gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      gvs[vyperStateTheory.assign_target_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def, vyperStateTheory.lift_option_def,
          vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
          vyperStateTheory.lift_sum_def, vyperStateTheory.set_scopes_def,
          AllCaseEqs()] >>
      imp_res_tac lift_sum_state >> imp_res_tac assign_result_state >>
      imp_res_tac write_abi_memory_frame >>
      imp_res_tac write_abi_immutables_frame >> gvs[])
  (* TopLevelVar *)
  >- (rpt strip_tac >> imp_res_tac assign_target_toplevel_logs)
  (* ImmutableVar *)
  >- (rpt strip_tac >>
      qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac get_immutables_state >> imp_res_tac lift_option_type_state >>
      imp_res_tac lift_sum_state >> gvs[] >>
      imp_res_tac set_immutable_logs >> imp_res_tac assign_result_state >>
      imp_res_tac write_abi_immutables_frame >> gvs[])
  (* TupleTargetV success *)
  >- (rpt strip_tac >>
      qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac type_check_state >> gvs[] >>
      first_x_assum drule >> imp_res_tac return_state >> gvs[])
  (* Constructor mismatch, base, cons, and fallback cases. *)
  >> rpt strip_tac
  >> pop_assum mp_tac
  >> simp[Once vyperStateTheory.assign_target_def,
          vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def,
          AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
  >> TRY (first_x_assum drule >> gvs[] >> NO_TAC)
  >> imp_res_tac return_state >> gvs[]
QED

Theorem assign_target_logs[local]:
  assign_target cx gv ao st = (res,st') ==> st'.logs = st.logs
Proof
  metis_tac[cj 1 assign_target_logs_mutual]
QED

Theorem assign_targets_logs[local]:
  assign_targets cx gvs vs st = (res,st') ==> st'.logs = st.logs
Proof
  metis_tac[cj 2 assign_target_logs_mutual]
QED

*)
Theorem case_stmt_annassign_logs[local]:
  (!tenv s0 tyv s1.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s0 =
       (INL tyv,s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (AnnAssign id typ e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[log_extends_refl] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!st res st'. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >> gvs[] >>
  imp_res_tac new_variable_logs >> gvs[log_extends_def]
QED

Theorem case_stmt_append_logs[local]:
  (!st res st'. eval_target_place cx bt st = (res,st') ==>
     log_extends st st') /\
  (!s0 p s1. eval_target_place cx bt s0 = (INL p,s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (Append bt e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >>
  qpat_x_assum `!s0 p s1. _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_target_place _ _ _ = _` kall_tac >>
  qpat_x_assum `bind (eval_target_place _ _) _ _ = _` kall_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac append_place_logs >> gvs[log_extends_def]
QED

Theorem case_expr_pop_logs[local]:
  (!st res st'. eval_target_place cx bt st = (res,st') ==>
     log_extends st st') ==>
  !st res st'. eval_expr cx (Pop ty bt) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac pop_place_logs >> gvs[log_extends_def]
QED

Theorem case_expr_builtin_logs[local]:
  (!s0 x s1.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s0 =
       (INL x,s1) /\ bt <> Len ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') /\
  (!s0 x s1.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s0 =
       (INL x,s1) /\ bt = Len ==>
     !st res st'. eval_expr cx (HD es) st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (Builtin ty bt es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.lift_sum_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  Cases_on `bt = Len` >> gvs[] >>
  TRY (gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, AllCaseEqs()] >>
       imp_res_tac result_array_length_state >> gvs[] >>
       first_x_assum (qspec_then `st` mp_tac) >>
       simp[vyperStateTheory.check_def, vyperStateTheory.type_check_def,
            vyperStateTheory.assert_def, vyperStateTheory.return_def] >> NO_TAC)
  >> `!st res st'. eval_exprs cx es st = (res,st') ==>
        log_extends st st'` by
       (first_x_assum (qspec_then `st` mp_tac) >>
        simp[vyperStateTheory.check_def, vyperStateTheory.type_check_def,
             vyperStateTheory.assert_def, vyperStateTheory.return_def])
  >> gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
         AllCaseEqs()]
  >> BasicProvers.FULL_CASE_TAC
  >> gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
  >> first_x_assum drule >> simp[]
QED

Theorem case_stmt_return_some_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Return (SOME e)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> imp_res_tac read_result_state >>
  imp_res_tac raise_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_stmt_expr_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Expr e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> imp_res_tac type_check_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem push_scope_log_extends[local]:
  push_scope st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.push_scope_def, vyperStateTheory.return_def] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem switch_BoolV_log_extends[local]:
  switch_BoolV cx tv f g st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `switch_BoolV cx _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac read_result_state >> gvs[log_extends_refl] >>
  rename1 `read_result cx tv _ = (INL bv,_)` >>
  Cases_on `bv = BoolV T` >>
  Cases_on `bv = BoolV F` >>
  gvs[vyperStateTheory.raise_def, log_extends_refl] >>
  first_x_assum drule >> simp[]
QED

Theorem finally_switch_BoolV_log_extends[local]:
  finally (switch_BoolV cx tv f g) pop_scope st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  irule finally_pop_scope_log_extends >>
  qexistsl [`switch_BoolV cx tv f g`, `res`] >>
  simp[] >> metis_tac[switch_BoolV_log_extends]
QED

Theorem case_stmt_if_logs[local]:
  (!s0 tv s1 s2 x s3.
     eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
     !st res st'. eval_stmts cx ss1 st = (res,st') ==> log_extends st st') /\
  (!s0 tv s1 s2 x s3.
     eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
     !st res st'. eval_stmts cx ss2 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (If e ss1 ss2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs(),
       vyperStateTheory.push_scope_def, vyperStateTheory.return_def] >>
  strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL tv,s_expr)` >>
  `log_extends st s_expr` by
    (qpat_x_assum `!s0 r s1. eval_expr _ _ _ = _ ==> _` drule >> simp[]) >>
  `!sb rb sb'. eval_stmts cx ss1 sb = (rb,sb') ==>
                log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 tv s1 s2 s3. _ ==> !st res st'. eval_stmts _ ss1 _ = _ ==> _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`,
                     `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[vyperStateTheory.push_scope_def, vyperStateTheory.return_def]) >>
  `!sb rb sb'. eval_stmts cx ss2 sb = (rb,sb') ==>
                log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 tv s1 s2 s3. _ ==> !st res st'. eval_stmts _ ss2 _ = _ ==> _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`,
                     `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[vyperStateTheory.push_scope_def, vyperStateTheory.return_def]) >>
  `log_extends (s_expr with scopes updated_by CONS FEMPTY) st'` by
    (drule finally_switch_BoolV_log_extends >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `log_extends s_expr (s_expr with scopes updated_by CONS FEMPTY)` by
    (irule log_extends_eq_logs >> simp[]) >>
  `log_extends s_expr st'` by
    (irule log_extends_trans >>
     qexists_tac `s_expr with scopes updated_by CONS FEMPTY` >> simp[]) >>
  irule log_extends_trans >> qexists_tac `s_expr` >> simp[]
QED
Theorem case_stmt_for_logs[local]:
  (!tenv s0 tyv s1 s2 vs s3 s4 x s5.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
       (INL tyv,s1) /\
     eval_iterator cx it s2 = (INL vs,s3) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 =
       (INL x,s5) ==>
     !st res st'. eval_for cx tyv id body vs st = (res,st') ==>
       log_extends st st') /\
  (!tenv s0 tyv s1.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
       (INL tyv,s1) ==>
     !st res st'. eval_iterator cx it st = (res,st') ==>
       log_extends st st') ==>
  !st res st'. eval_stmt cx (For id typ it n body) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then MATCH_MP_TAC >>
  conj_tac
  >- (rpt strip_tac >> drule lift_option_type_state >>
      disch_then SUBST1_TAC >> irule log_extends_refl) >>
  rpt strip_tac >> pop_assum (assume_tac o BETA_RULE) >>
  rename1 `lift_option_type _ _ st = (INL tyv,s_type)` >>
  qpat_x_assum `!tenv s0 tyv s1. _`
    (qspecl_then [`get_tenv cx`, `st`, `tyv`, `s_type`] mp_tac) >>
  qpat_assum `lift_option_type _ _ st = (INL tyv,s_type)`
    (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  qpat_x_assum `!tenv s0 tyv s1 s2 vs s3 s4 x s5. _`
    (qspecl_then [`get_tenv cx`, `st`, `tyv`, `s_type`] mp_tac) >>
  qpat_assum `lift_option_type _ _ st = (INL tyv,s_type)`
    (fn th => simp_tac bool_ss [th]) >> strip_tac >>
  drule bind_log_extends_forward >> disch_then MATCH_MP_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!st res st'. eval_iterator _ _ _ = _ ==> _` drule >>
      simp[]) >>
  rpt strip_tac >>
  pop_assum (assume_tac o BETA_RULE o
             REWRITE_RULE [vyperStateTheory.ignore_bind_def]) >>
  drule bind_log_extends_forward >> disch_then MATCH_MP_TAC >>
  conj_tac
  >- (rpt strip_tac >> drule check_state >>
      disch_then SUBST1_TAC >> irule log_extends_refl) >>
  rpt strip_tac >> pop_assum (assume_tac o BETA_RULE) >>
  first_x_assum drule_all >> simp[]
QED

Theorem case_stmt_raise_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Raise (RaiseReason e)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED

Theorem case_stmt_raise_custom_error_logs[local]:
  (!id positional kwargs tops params es.
     err = CustomError id positional kwargs /\
     get_module_code cx (FST id) = SOME tops /\
     lookup_custom_error_args_in (SND id) tops = SOME params /\
     order_custom_error_args params err = SOME es ==>
     !s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Raise (RaiseCustomError err)) st = (res,st') ==>
    log_extends st st'
Proof
  Cases_on `err` >> rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt CASE_TAC >> rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def, AllCaseEqs(),
      log_extends_refl] >>
  imp_res_tac lift_option_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem case_stmt_assert_logs[local]:
  (!s0 tv s1. eval_expr cx e s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx se st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e (AssertReason se)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!s0 tv s1. _` drule >> strip_tac >>
  drule switch_BoolV_log_extends >> disch_then irule >>
  conj_tac >- (simp[vyperStateTheory.return_def, log_extends_refl]) >>
  rpt strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def,
      AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem case_stmt_assert_custom_error_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 tv s1 id positional kwargs tops params es.
     eval_expr cx e s0 = (INL tv,s1) /\
     err = CustomError id positional kwargs /\
     get_module_code cx (FST id) = SOME tops /\
     lookup_custom_error_args_in (SND id) tops = SOME params /\
     order_custom_error_args params err = SOME es ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (Assert e (AssertCustomError err)) st = (res,st') ==>
    log_extends st st'
Proof
  Cases_on `err` >> rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >>
  rpt CASE_TAC >> rpt strip_tac >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), vyperStateTheory.return_def,
      vyperStateTheory.raise_def, vyperStateTheory.bind_def] >>
  imp_res_tac lift_option_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[] >>
  rpt (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem case_stmt_assert_bare_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e AssertBare) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >>
  drule switch_BoolV_log_extends >> disch_then irule >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       log_extends_refl]
QED

Theorem case_stmt_assert_unreachable_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e AssertUnreachable) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >>
  drule switch_BoolV_log_extends >> disch_then irule >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       log_extends_refl]
QED

Theorem case_stmt_log_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Log id es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_state >> gvs[] >>
  imp_res_tac push_log_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  simp[log_extends_append]
QED

Theorem case_expr_name_logs[local]:
  eval_expr cx (Name ty id) st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl]
QED

Theorem lookup_global_log_extends[local]:
  lookup_global cx src id st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> imp_res_tac lookup_global_state >>
  gvs[log_extends_refl]
QED

Theorem lookup_flag_mem_log_extends[local]:
  lookup_flag_mem cx nsid mid st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> imp_res_tac lookup_flag_mem_state >>
  gvs[log_extends_refl]
QED

Theorem case_expr_toplevel_name_logs[local]:
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
  log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  metis_tac[lookup_global_log_extends]
QED

Theorem case_expr_flag_member_logs[local]:
  eval_expr cx (FlagMember ty nsid mid) st = (res,st') ==>
  log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  metis_tac[lookup_flag_mem_log_extends]
QED

Theorem case_expr_if_logs[local]:
  (!s0 tv s1. eval_expr cx e1 s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx e2 st = (res,st') ==> log_extends st st') /\
  (!s0 tv s1. eval_expr cx e1 s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx e3 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (IfExp ty e1 e2 e3) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >> strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e2 _ = _ ==> _`
    drule >> strip_tac >>
  qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e3 _ = _ ==> _`
    drule >> strip_tac >>
  qpat_x_assum `bind (eval_expr cx e1) _ _ = _` kall_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  rpt strip_tac >> gvs[] >> imp_res_tac conditional_result_state >>
  gvs[log_extends_refl] >>
  drule switch_BoolV_log_extends >> disch_then irule >> simp[]
QED

Theorem case_expr_struct_lit_logs[local]:
  (!ks. ks = MAP FST kes ==>
     !s0 r s1. eval_exprs cx (MAP SND kes) s0 = (r,s1) ==>
       log_extends s0 s1) ==>
  !st res st'. eval_expr cx (StructLit ty sid kes) st = (res,st') ==>
    log_extends st st'
Proof
  PairCases_on `sid` >> rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac equality_guard_specialize >>
  first_x_assum drule >> simp[]
QED

Theorem transfer_value_logs[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  st'.logs = st.logs
Proof

  strip_tac >> drule concrete_send_step_locals >> simp[]
QED

Theorem eval_send_log_extends:
  eval_send cx has_gas vs st = (res,st') ==> log_extends st st'
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def, log_extends_refl] >>
  Cases_on `t` >- simp[eval_send_def, raise_def, log_extends_refl] >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def,
       get_transient_storage_def, lift_option_def, lift_option_type_def,
       check_def, update_accounts_def, update_transient_def, append_logs_def,
       vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.adopt_call_outcome_equation, LET_THM, UNCURRY,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  strip_tac >>
  gvs[AllCaseEqs(), log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem case_expr_send_logs[local]:
  (!s0 s1. type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s0 =
             (INL (),s1) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (Call ty (Send has_gas) es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, log_extends_refl] >>
  first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> strip_tac >>
  rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  drule eval_send_log_extends >> strip_tac >>
  drule_all log_extends_trans >> simp[]
QED

Theorem case_expr_selfdestruct_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty SelfDestructTarget es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac transfer_value_logs >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem finally_log_extends[local]:
  finally f g st = (res,st') ==>
  (!r s1. f st = (r,s1) ==> log_extends st s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem set_scopes_log_extends[local]:
  set_scopes scopes st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem acquire_nonreentrant_lock_log_extends[local]:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on
    `lookup_storage (n2w slot)
       (vfmExecution$lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[vyperInterpreterTheory.acquire_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem release_nonreentrant_lock_log_extends[local]:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  log_extends st st'
Proof
  simp[vyperInterpreterTheory.release_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem intcall_cleanup_log_extends[local]:
  (do pop_function prev;
      if nr /\ ~is_view then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()
   od) st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `nr` >> Cases_on `is_view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.pop_function_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac set_scopes_log_extends >>
  imp_res_tac release_nonreentrant_lock_log_extends >>
  imp_res_tac return_state >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem handle_function_log_extends[local]:
  handle_function ex st = (res,st') ==> log_extends st st'
Proof
  Cases_on `ex` >>
  simp[oneline vyperInterpreterTheory.handle_function_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[log_extends_refl]
QED

Theorem intcall_try_body_log_extends[local]:
  (try (do eval_stmts cxf body; return NoneV od) handle_function) st =
    (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac handle_function_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem intcall_defaults_log_extends[local]:
  finally (do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od)
          (set_scopes prev) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
     log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.set_scopes_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `log_extends (st with scopes := [FEMPTY]) s''` mp_tac >>
  simp[log_extends_def]
QED

Theorem intcall_defaults_exact_log_extends[local]:
  finally (do x <- set_scopes [FEMPTY];
              eval_exprs cxd needed_dflts
           od)
          (set_scopes prev) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
     log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.set_scopes_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `log_extends (st with scopes := [FEMPTY]) s''` mp_tac >>
  simp[log_extends_def]
QED
Theorem intcall_scoped_defaults_bind_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od)
        (set_scopes prev);
      k prev dflt_vs
   od) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
             log_extends s0 s1) ==>
  (!prev dflt_vs s0 r s1. k prev dflt_vs s0 = (r,s1) ==>
                          log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     rpt strip_tac >>
     drule intcall_defaults_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED

Theorem sum_result_case_log_extends[local]:
  (case q of INL x => k x st | INR e => (INR e,st)) = (res,st') ==>
  (!x res st'. k x st = (res,st') ==> log_extends st st') ==>
  log_extends st st'
Proof
  Cases_on `q` >> simp[log_extends_refl] >> metis_tac[]
QED

Theorem intcall_body_finally_log_extends[local]:
  finally (try (do eval_stmts cxf body; return NoneV od) handle_function)
    (do pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule finally_log_extends >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> drule intcall_cleanup_log_extends >> simp[]) >>
  rpt strip_tac >>
  drule intcall_try_body_log_extends >> disch_then irule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem intcall_cleanup_exact_log_extends[local]:
  (do x <- pop_function prev;
      if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()
   od) st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `nr` >> Cases_on `mut` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.pop_function_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac set_scopes_log_extends >>
  imp_res_tac release_nonreentrant_lock_log_extends >>
  imp_res_tac return_state >> gvs[log_extends_refl] >>
  metis_tac[log_extends_trans]
QED

Theorem intcall_try_body_exact_log_extends[local]:
  (try (do x <- eval_stmts cxf body; return NoneV od) handle_function) st =
    (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac handle_function_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem intcall_body_finally_exact_log_extends[local]:
  finally (try (do x <- eval_stmts cxf body; return NoneV od) handle_function)
    (do x <- pop_function prev;
        if nr /\ mut <> View /\ mut <> Pure then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule finally_log_extends >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> drule intcall_cleanup_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  drule intcall_try_body_exact_log_extends >> disch_then irule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem intcall_needed_dflts_index[local]:
  e <= a /\ a <= e + d ==> d - (a - e) = e + d - a
Proof
  decide_tac
QED

Theorem push_function_logs[local]:
  push_function src_fn sc cx st = (res,st') ==>
  st'.logs = st.logs
Proof
  simp[vyperInterpreterTheory.push_function_def,
       vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem intcall_post_defaults_log_extends[local]:
  (do env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot =>
                 acquire_nonreentrant_lock cx.txn.target slot
                   (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.push_function_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl] >>
  `log_extends s'' s'⁴'` by
    (qpat_x_assum `(if nr then _ else _) _ = _` mp_tac >>
     Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     rpt strip_tac >>
     imp_res_tac acquire_nonreentrant_lock_log_extends >>
     gvs[log_extends_refl]) >>
  `log_extends (s'⁴' with scopes := [env]) s'⁵'` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     strip_tac >>
     drule intcall_body_finally_exact_log_extends >>
     simp[]) >>
  irule log_extends_trans >>
  qexists `s'⁴'` >> simp[] >>
  irule log_extends_trans >>
  qexists `s'⁴' with scopes := [env]` >>
  simp[log_extends_eq_logs]
QED

Theorem intcall_post_defaults_guarded_log_extends[local]:
  (do env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot =>
                 acquire_nonreentrant_lock cx.txn.target slot
                   (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) sg2 = (res,st') ==>
  (!env sg3 rtv sg4 sg5 cxf sg6.
     lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments" sg2 = (INL env,sg3) ==>
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" sg3 = (INL rtv,sg4) ==>
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ()) sg4 = (INL (),sg5) ==>
     push_function (src_id_opt,fn) env cx sg5 = (INL cxf,sg6) ==>
     !s0 r s1. eval_stmts cxf body s0 = (r,s1) ==>
                log_extends s0 s1) ==>
  log_extends sg2 st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl] >>
  `log_extends s'' s'⁴'` by
    (qpat_x_assum `(if nr then _ else _) _ = _` mp_tac >>
     Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     rpt strip_tac >>
     imp_res_tac acquire_nonreentrant_lock_log_extends >>
     gvs[log_extends_refl]) >>
  `log_extends s'⁴' s'⁵'` by
    (irule log_extends_eq_logs >>
     imp_res_tac push_function_logs >> sym_tac >>
     first_assum MATCH_ACCEPT_TAC) >>

  all_tac >~ [`push_function _ _ _ _ = (INR _,_)`] >-
    metis_tac[log_extends_trans] >>
  `log_extends s'⁵' s'⁶'` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     strip_tac >>
     drule intcall_body_finally_exact_log_extends >> simp[]) >>
  metis_tac[log_extends_trans]
QED

Theorem intcall_success_continuation_guarded_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do x <- set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         od) (set_scopes prev);
      env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  (!sg prev sg1 dflt_vs sg2 env sg3 rtv sg4 sg5 cxf sg6.
     get_scopes sg = (INL prev,sg1) ==>
     finally
       (do x <- set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od) (set_scopes prev) sg1 = (INL dflt_vs,sg2) ==>
     lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments" sg2 = (INL env,sg3) ==>
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" sg3 = (INL rtv,sg4) ==>
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ()) sg4 = (INL (),sg5) ==>
     push_function (src_id_opt,fn) env cx sg5 = (INL cxf,sg6) ==>
     !s0 r s1. eval_stmts cxf body s0 = (r,s1) ==>
                log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `!sg prev sg1 dflt_vs sg2 env sg3 rtv sg4 sg5 cxf sg6. _`
    (mk_asm "guarded") >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >>
        asm "guarded" drule >> disch_then drule >>
        disch_then assume_tac >>
        drule intcall_post_defaults_guarded_log_extends >> simp[]) >>
     rpt strip_tac >>
     drule intcall_defaults_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED

Theorem intcall_success_continuation_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do x <- set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         od) (set_scopes prev);
      env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1.
     eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >>
        drule intcall_post_defaults_log_extends >> simp[]) >>
     rpt strip_tac >>
     drule intcall_defaults_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED

(* Earlier inlined call framing, replaced by the effects boundary below.
Theorem log_call_leaves[local]:
  state_rel_frame log_extends (vyperState$return x) /\
  state_rel_frame log_extends (vyperState$raise e) /\
  state_rel_frame log_extends (λs. vyperState$return (g s) s) /\
  state_rel_frame log_extends (type_check b msg) /\
  state_rel_frame log_extends (check b msg) /\
  state_rel_frame log_extends (lift_option opt msg) /\
  state_rel_frame log_extends (lift_option_type opt msg) /\
  state_rel_frame log_extends (lift_sum_runtime rs) /\
  state_rel_frame log_extends get_accounts /\
  state_rel_frame log_extends get_transient_storage /\
  state_rel_frame log_extends (update_accounts fa) /\
  state_rel_frame log_extends (update_transient ft) /\
  state_rel_frame log_extends (append_logs ls) /\
  state_rel_frame log_extends (take_call_outcome addr data amount) /\
  state_rel_frame log_extends (adopt_call_outcome rq co)
Proof
  simp[state_rel_frame_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.type_check_def, vyperStateTheory.check_def,
    vyperStateTheory.assert_def, vyperStateTheory.lift_option_def,
    vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_runtime_def,
    vyperStateTheory.get_accounts_def, vyperStateTheory.get_transient_storage_def,
    vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
    vyperStateTheory.append_logs_def, log_extends_def,
    rich_listTheory.IS_PREFIX_REFL, rich_listTheory.IS_PREFIX_APPEND,
    vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (rpt CASE_TAC >> simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
    rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC) >>
  Cases_on `take_call_outcome addr data amount st` >>
  drule take_call_outcome_frame >>
  simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[rich_listTheory.IS_PREFIX_REFL]
QED

local
  val trans = log_extends_trans |> GEN_ALL;
  val relation = ``log_extends``;
  val bind = state_rel_frame_bind_guarded |> Q.INST [`R` |-> `log_extends`]
    |> SIMP_RULE bool_ss [EQT_INTRO trans];
  val leaves = CONJUNCTS log_call_leaves;
  fun branch (g as (old,_)) =
    (BasicProvers.PURE_TOP_CASE_TAC >> (fn (asl,w) => simp_tac (srw_ss())
      (map ASSUME (List.filter (fn a => not (is_forall a) andalso
        not (List.exists (aconv a) old)) asl)) (asl,w))) g;
in
  val CALL_LOG_STEP_TAC = FIRST [MATCH_ACCEPT_TAC trans,
    FIRST (map MATCH_ACCEPT_TAC leaves),
    MATCH_MP_TAC bind >> conj_tac,
    CONV_TAC (RAND_CONV BETA_CONV),
    CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
    CHANGED_TAC (simp_tac (srw_ss()) [LET_THM, pairTheory.UNCURRY]),
    gen_tac, strip_tac, branch];
  val CALL_LOG_TAC = rpt CALL_LOG_STEP_TAC;
end;
*)
(* Compositional proof control for the actual activated call clause. *)
Definition log_monad_def:
  log_monad f <=> !s r t. f s = (r,t) ==> log_extends s t
End

Theorem log_monad_bind_guarded[local]:
  log_monad f /\
  (!s v t. f s = (INL v,t) ==> log_monad (g v)) ==>
  log_monad (vyperState$bind f g)
Proof
  simp[log_monad_def, vyperStateTheory.bind_def] >> rpt strip_tac >>
  Cases_on `f s` >> Cases_on `q` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all log_extends_trans >> simp[]
QED

Theorem log_monad_primitives[local]:
  log_monad (return v) /\ log_monad (\s. return (g s) s) /\
  log_monad (raise e) /\
  log_monad (type_check b msg) /\ log_monad (check b msg) /\
  log_monad (lift_option opt msg) /\ log_monad (lift_option_type opt msg) /\
  log_monad (lift_sum_runtime rs) /\ log_monad get_accounts /\
  log_monad get_transient_storage /\ log_monad (update_accounts upd) /\
  log_monad (update_transient upd_t) /\ log_monad (append_logs logs) /\
  log_monad (adopt_call_outcome rq co)
Proof
  simp[log_monad_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.check_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_sum_runtime_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       append_logs_def, adopt_call_outcome_equation] >>
  rpt strip_tac >> rpt CASE_TAC >>
  gvs[option_CASE_rator, sum_CASE_rator, AllCaseEqs(),
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      log_extends_def, rich_listTheory.IS_PREFIX_APPEND,
      rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_monad_take[local]:
  log_monad (take_call_outcome target calldata value_opt)
Proof
  simp[log_monad_def] >> rpt strip_tac >>
  drule take_call_outcome_frame >>
  simp[evaluation_state_component_equality, log_extends_def,
       rich_listTheory.IS_PREFIX_REFL]
QED

(* Index primitive leaves once; never traverse their continuations or the
   large guarded IHs just to recognise a primitive computation. *)
val EXTCALL_LOG_MONAD_LEAF_TAC =
  let
    val structural = Net.insert
      (concl log_monad_bind_guarded |> dest_imp |> snd,
       MATCH_MP_TAC log_monad_bind_guarded >> conj_tac) Net.empty
    val leaves = List.foldl (fn (th,net) =>
      Net.insert (concl th, MATCH_ACCEPT_TAC th) net) structural
      (log_monad_take :: CONJUNCTS log_monad_primitives)
  in
    fn (asl,w) => FIRST (Net.match w leaves) (asl,w)
  end;

(* Reduce exposed applications only, not continuation arguments. *)
val extcall_log_head_conv =
  let
    val reduce = FIRST_CONV
      [BETA_CONV, REWR_CONV pair_case_thm, REWR_CONV UNCURRY]
    fun head tm = (reduce ORELSEC RATOR_CONV head) tm
  in head end;

(* Preserve CASE_TAC branch order without its broad datatype rewrite set.
   Only fresh branch facts, never guarded IHs, become rewrite rules. *)
fun EXTCALL_LOG_MONAD_CASE_TAC (g as (old,_)) =
  let
    fun simplify (asl,w) =
      let
        val fresh = List.filter (fn a => not (is_forall a) andalso
          not (List.exists (aconv a) old)) asl
        val rules = map ASSUME fresh
      in
        simp_tac bool_ss
          (optionTheory.option_CLAUSES :: pair_case_thm :: UNCURRY :: rules) >>
        RULE_ASSUM_TAC (fn th =>
          if is_forall (concl th) then th else REWRITE_RULE rules th) >>
        MAP_EVERY assume_tac rules
      end (asl,w)
  in
    (BasicProvers.PURE_CASE_TAC >> simplify) g
  end;

val EXTCALL_LOG_MONAD_STEP_TAC =
  FIRST [
    first_assum ACCEPT_TAC,
    EXTCALL_LOG_MONAD_LEAF_TAC,
    CONV_TAC (HO_REWR_CONV FORALL_PROD),
    CONV_TAC (RAND_CONV extcall_log_head_conv),
    gen_tac, strip_tac, conj_tac,
    CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
    CONV_TAC (RAND_CONV ETA_CONV),
    CHANGED_TAC (fn (asl,w) =>
      simp_tac bool_ss (pair_case_thm :: UNCURRY ::
        List.map ASSUME (List.filter is_eq asl)) (asl,w)),
    EXTCALL_LOG_MONAD_CASE_TAC];

val EXTCALL_LOG_MONAD_TAC = rpt EXTCALL_LOG_MONAD_STEP_TAC;

Theorem eval_ext_call_log_monad[local]:
  log_monad (eval_ext_call cx static skip_check sig opts vs)
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  simp_tac bool_ss [eval_ext_call_def, eval_ext_call_effects_def, LET_THM] >>
  EXTCALL_LOG_MONAD_TAC
QED

Theorem eval_ext_call_log_extends:
  eval_ext_call cx static skip_check sig opts vs st = (res,st') ==>
  log_extends st st'
Proof
(* Legacy inline proof.
  `state_rel_frame log_extends (eval_ext_call cx static skip_check sig opts vs)`
    suffices_by metis_tac[state_rel_frame_result] >>
  PairCases_on `sig` >> Cases_on `vs` >>
  simp_tac bool_ss [eval_ext_call_def, LET_THM] >>
  NTAC 4 (TRY CALL_LOG_STEP_TAC) >>
  NTAC 4 (TRY CALL_LOG_STEP_TAC) >>
  NTAC 4 (TRY CALL_LOG_STEP_TAC) >>
  CALL_LOG_TAC
*)
  mp_tac (REWRITE_RULE [log_monad_def] eval_ext_call_log_monad) >> simp[]
QED

Theorem case_expr_ext_call_logs[local]:
  (!s0 r s1. eval_exprs cx (TAKE 1 es) s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 target s1. eval_exprs cx (TAKE 1 es) s0 = (INL target,s1) ==>
    !st res st'. eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) st = (res,st') ==>
      log_extends st st') /\
  (!s0 target s1 s2 results s3.
    eval_exprs cx (TAKE 1 es) s0 = (INL target,s1) /\
    eval_expr_results cx (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) s2 = (INL results,s3) ==>
    !st res st'. eval_exprs cx (DROP (1 + LENGTH (FST (SND sig))) es) st = (res,st') ==>
      log_extends st st') ==>
  !st res st'.
    eval_expr cx (Call ty (ExtCall static skip_check sig opts) es drv) st =
      (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  imp_res_tac eval_ext_call_log_extends >>
  metis_tac[log_extends_trans]
QED

Theorem raw_call_tail_log_extends[local]:
  (do x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      x <- append_logs emitted_logs;
      if flags.rcf_revert_on_failure then do
        x <- if success then return () else raise (Error (RevertData returnData));
        if flags.rcf_max_outsize = 0 then return (Value NoneV)
        else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
      od else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
      else return (Value (ArrayV (TupleV
        [BoolV success; BytesV (TAKE flags.rcf_max_outsize returnData)])))
   od) st = (res,st') ==> log_extends st st'
Proof
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperStateTheory.append_logs_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       log_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem eval_raw_call_log_extends:
  eval_raw_call cx flags target_addr calldata amount st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)` >>
  fs[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def,
       get_transient_storage_def, log_extends_refl] >>
  Cases_on `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage` >>
  simp[lift_option_def, bind_def, return_def, raise_def, log_extends_refl] >>
  rename1 `run_raw_call _ _ _ _ _ _ _ = SOME call_result` >>
  PairCases_on `call_result` >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `call_result0` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[update_accounts_def, update_transient_def, append_logs_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       log_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem case_expr_raw_call_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty (RawCallTarget flags) es drv) st =
    (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  first_x_assum drule >> strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  drule eval_raw_call_log_extends >> strip_tac >>
  drule_all log_extends_trans >> simp[]
QED

Theorem case_expr_raw_call_calldata_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) st =
    (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  first_x_assum drule >> strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  drule eval_raw_call_log_extends >> strip_tac >>
  drule_all log_extends_trans >> simp[]
QED

Theorem case_expr_raw_log_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty RawLog es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac push_log_log_extends >> imp_res_tac return_state >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  simp[log_extends_append]
QED

Theorem case_expr_raw_revert_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty RawRevert es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_state >> imp_res_tac raise_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_expr_attribute_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Attribute ty e id) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac select_result_state >> gvs[log_extends_refl] >>
  first_x_assum drule >> simp[]
QED

(* Obsolete eager-only helper retained for reference; TypeBuiltin now uses
   the guarded ABI/eager IHs in LOG_ABI_TAC below.
Theorem case_expr_type_builtin_logs[local]:
  (!s0 s1.
     type_check (type_builtin_args_length_ok tb (LENGTH es))
       "TypeBuiltin args" s0 = (INL (),s1) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (TypeBuiltin ty tb typ es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_guard_specialize >>
  imp_res_tac type_check_state >> imp_res_tac lift_sum_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED

*)

Theorem case_eval_exprs_nil_logs[local]:
  eval_exprs cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
       log_extends_refl]
QED

Theorem case_eval_exprs_cons_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 tv s1 s2 v s3.
     eval_expr cx e s0 = (INL tv,s1) /\
     read_result cx tv s2 = (INL v,s3) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_exprs cx (e::es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem case_eval_expr_results_nil_logs[local]:
  eval_expr_results cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
       log_extends_refl]
QED

Theorem case_eval_expr_results_cons_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 tv s1. eval_expr cx e s0 = (INL tv,s1) ==>
     !st res st'. eval_expr_results cx es st = (res,st') ==>
       log_extends st st') ==>
  !st res st'. eval_expr_results cx (e::es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

local
  fun last_imp_ante tm =
    let
      val (_,body) = boolSyntax.strip_forall tm
      val (ante,conseq) = boolSyntax.dest_imp body
      val (_,next) = boolSyntax.strip_forall conseq
    in
      if boolSyntax.is_imp next then
        let val (depth,last) = last_imp_ante conseq in (depth + 1,last) end
      else (1,ante)
    end

  fun is_guarded_eval_ih name tm =
    let
      val (depth,ante) = last_imp_ante tm
      val (lhs,_) = boolSyntax.dest_eq ante
      val (head,_) = boolSyntax.dest_strip_comb lhs
    in
      depth > 1 andalso head = name
    end handle _ => false

  fun specialize_guard_then 0 ttac th = ttac th
    | specialize_guard_then n ttac th =
        first_assum (fn ath =>
          specialize_guard_then (n - 1) ttac
            (MATCH_MP (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] th) ath))
in
  val specialize_guard_then = specialize_guard_then
  val is_guarded_eval_expr_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_expr"
  val is_guarded_eval_exprs_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_exprs"
  val is_guarded_eval_stmts_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_stmts"
  fun TOP_CASE_IF_PRESENT_TAC g =
    ((BasicProvers.TOP_CASE_TAC ORELSE ALL_TAC) g)
  fun unfold_last_eval_ante_conv tm =
    if boolSyntax.is_forall tm then
      QUANT_CONV unfold_last_eval_ante_conv tm
    else if boolSyntax.is_imp tm then
      let
        val (_,conseq) = boolSyntax.dest_imp tm
        val (_,body) = boolSyntax.strip_forall conseq
      in
        if boolSyntax.is_imp body then
          RAND_CONV unfold_last_eval_ante_conv tm
        else
          LAND_CONV
            (LAND_CONV
              (SCONV [Once vyperInterpreterTheory.evaluate_def,
                      vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def,
                      vyperStateTheory.return_def,
                      vyperStateTheory.raise_def])) tm
      end
    else raise ERR "unfold_last_eval_ante_conv" "expected guarded implication"
  fun commute_outer_ante_conv tm =
    if boolSyntax.is_forall tm then
      QUANT_CONV commute_outer_ante_conv tm
    else if boolSyntax.is_imp tm then
      LAND_CONV (REWR_CONV CONJ_COMM) tm
    else raise ERR "commute_outer_ante_conv" "expected implication"
  fun APPLY_CASE_HELPER_TAC th =
    FIRST_PROVE
      [MATCH_ACCEPT_TAC th,
       rpt gen_tac >> disch_tac >> ho_match_mp_tac th >>
       TRY (qpat_x_assum `_ /\ _` strip_assume_tac) >>
       rpt conj_tac >> first_assum MATCH_ACCEPT_TAC]
  fun APPLY_NORMALIZED_CASE_HELPER_TAC th =
    APPLY_CASE_HELPER_TAC (CONV_RULE unfold_last_eval_ante_conv th)
  val eval_case_helpers =
    [case_iterator_array_logs, case_iterator_range_logs,
     case_eval_for_nil_logs, case_eval_for_cons_logs,
     case_eval_stmts_nil_logs, case_eval_stmts_cons_logs,
     case_stmt_annassign_logs, case_stmt_append_logs, case_stmt_return_some_logs,
     case_stmt_expr_logs, case_stmt_if_logs, case_stmt_for_logs,
     case_stmt_raise_logs, case_stmt_raise_custom_error_logs,
     case_stmt_assert_logs, case_stmt_assert_custom_error_logs,
     case_stmt_assert_bare_logs, case_stmt_assert_unreachable_logs,
     case_stmt_log_logs,
     case_expr_name_logs, case_expr_toplevel_name_logs,
     case_expr_flag_member_logs, lookup_global_log_extends,
     lookup_flag_mem_log_extends, case_expr_subscript_logs, case_expr_pop_logs,
     case_expr_builtin_logs, case_expr_if_logs, case_expr_struct_lit_logs,
     case_expr_send_logs, case_expr_selfdestruct_logs,
     case_expr_ext_call_logs,
     case_expr_raw_call_logs, case_expr_raw_call_calldata_logs,
     case_expr_raw_log_logs, case_expr_raw_revert_logs,
     case_expr_attribute_logs,
     case_eval_exprs_nil_logs, case_eval_exprs_cons_logs,
     case_eval_expr_results_nil_logs, case_eval_expr_results_cons_logs]
end

Theorem conjunction_guard_specialize_probe[local]:
  (!x y. f x = a /\ g y = b ==> P x y) ==>
  f u = a ==>
  g v = b ==>
  P u v
Proof
  rpt strip_tac >>
  first_x_assum (specialize_guard_then 2 MATCH_ACCEPT_TAC)
QED

Theorem log_abi_relation[local]:
  (!s t u. log_extends s t /\ log_extends t u ==> log_extends s u) /\
  (!s mem. log_extends s (s with abi_memory := mem)) /\
  (!s mem. log_extends s (s with abi_immutables := mem))
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL] >>
  metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem log_abi_pure_frames[local]:
  state_rel_frame log_extends (vyperState$return x) /\
  state_rel_frame log_extends (vyperState$raise e) /\
  state_rel_frame log_extends (type_check b msg) /\
  state_rel_frame log_extends (check b msg) /\
  state_rel_frame log_extends (lift_option opt msg) /\
  state_rel_frame log_extends (lift_option_type opt msg) /\
  state_rel_frame log_extends (lift_sum rs) /\
  state_rel_frame log_extends (read_result cx tv) /\
  state_rel_frame log_extends (pop_place cx target)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule log_extends_eq_logs >>
  FIRST [drule return_state, drule raise_state, drule type_check_state,
    drule check_state, drule lift_option_state, drule lift_option_type_state,
    drule lift_sum_state, drule read_result_state,
    drule pop_place_logs] >> simp[]
QED

local
  val relation = ``log_extends``;
  fun spec th = ISPEC relation (GEN (first (fn v => fst (dest_var v) = "R")
    (free_vars (concl th))) th);
  val result = spec state_rel_frame_result;
  val bind = SIMP_RULE bool_ss [EQT_INTRO (CONJUNCT1 log_abi_relation)]
    (spec state_rel_frame_bind_guarded);
  val finally = SIMP_RULE bool_ss [EQT_INTRO (CONJUNCT1 log_abi_relation)]
    (spec state_rel_frame_finally);
  val leaves = MATCH_MP (spec state_rel_frame_abi_place) log_abi_relation ::
    CONJUNCTS (MATCH_MP (spec state_rel_frame_abi_primitives) log_abi_relation) @
    CONJUNCTS log_abi_pure_frames;
  fun ih (asl,w) =
    let
      val norm = SIMP_RULE bool_ss [oneTheory.one, vyperStateTheory.ignore_bind_def];
      val facts = List.concat (map (CONJUNCTS o norm o ASSUME) asl);
      fun discharge th = if is_imp (snd (strip_forall (concl th))) then
        discharge (tryfind (MATCH_MP th) facts) else th;
    in FIRST (map (fn th => fn g => MATCH_ACCEPT_TAC
      (discharge (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] th)) g) facts) (asl,w) end;
in
  val LOG_ABI_TAC =
    rpt (fn g as (_,w) => if is_forall w andalso
      type_of (#1 (dest_forall w)) <> ``:evaluation_state`` then gen_tac g else NO_TAC g) >>
    (fn g as (_,w) => if is_imp w then strip_tac g else ALL_TAC g) >>
    CONV_TAC (REWR_CONV (GSYM result)) >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [vyperInterpreterTheory.evaluate_def])) >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM result]) >>
    rpt (FIRST [MATCH_ACCEPT_TAC (GEN_ALL log_extends_trans),
      FIRST (map MATCH_ACCEPT_TAC leaves), ih,
      MATCH_MP_TAC bind >> conj_tac, MATCH_MP_TAC finally >> conj_tac,
      CONV_TAC (RAND_CONV BETA_CONV),
      CONV_TAC (RAND_CONV (REWR_CONV vyperStateTheory.ignore_bind_def)),
      CONV_TAC (RAND_CONV (REWR_CONV vyperInterpreterTheory.switch_BoolV_def)),
      CHANGED_TAC (simp_tac bool_ss [pairTheory.UNCURRY, pairTheory.pair_case_thm]),
      gen_tac, strip_tac,
      CHANGED_TAC (fn (asl,w) => simp_tac (srw_ss())
        (map ASSUME (List.filter (not o is_forall) asl)) (asl,w)),
      BasicProvers.PURE_TOP_CASE_TAC]);
end;

Theorem case_abi_expr_pop_logs[local]:
  (!st res st'. eval_target_place cx target st = (res,st') ==>
     log_extends st st') ==>
  !st res st'. eval_abi_expr cx (Pop ty target) st = (res,st') ==>
    log_extends st st'
Proof
  LOG_ABI_TAC
QED

(* Legacy eager-target dispatcher, superseded by place/ABI dispatch below.
val REST_ATOMIC_DISPATCH_TAC =
  FIRST
    ([LOG_ABI_TAC >> NO_TAC,
      rpt gen_tac >> strip_tac >>
      rename1 `eval_expr _ (TypeBuiltin _ tb _ _)` >>
      Cases_on `tb` >> gvs[] >> LOG_ABI_TAC >> NO_TAC,
      rpt gen_tac >> disch_tac >>
      ho_match_mp_tac
        (CONV_RULE commute_outer_ante_conv case_stmt_assign_logs) >>
      first_assum MATCH_ACCEPT_TAC,
      rpt gen_tac >> strip_tac >>
      ho_match_mp_tac case_eval_targets_cons_logs >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC,
      rpt gen_tac >> strip_tac >>
*)
val PLACE_LOG_CASE_TAC =
  rpt strip_tac >>
  FIRST [qpat_x_assum `eval_stmt _ (Assign _ _) _ = _` mp_tac,
         qpat_x_assum `eval_stmt _ (AugAssign _ _ _ _) _ = _` mp_tac,
         qpat_x_assum `eval_base_place _ _ _ = _` mp_tac,
         qpat_x_assum `eval_target_place _ _ _ = _` mp_tac,
         qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac,
         qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac] >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs(),
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
  imp_res_tac read_place_state >> imp_res_tac read_result_state >>
  imp_res_tac place_type_value_state >> imp_res_tac get_place_state >>
  imp_res_tac lookup_global_state >> imp_res_tac extend_place_state >>
  imp_res_tac read_result_state >>
  imp_res_tac read_result_state >> gvs[log_extends_refl] >>
  imp_res_tac write_place_logs >>
  gvs[vyperValueTheory.value_CASE_rator, vyperValueTheory.array_value_CASE_rator, AllCaseEqs(),
      vyperStateTheory.raise_def, log_extends_refl] >>
  rpt (PRED_ASSUM
    (fn tm => let val (_,body) = boolSyntax.strip_forall tm
                  val (_,tail) = boolSyntax.dest_imp body
              in boolSyntax.is_forall tail end handle HOL_ERR _ => false)
    (drule_all_then assume_tac)) >>
  metis_tac[log_extends_trans, log_extends_eq_logs];

val REST_ATOMIC_DISPATCH_TAC =
  FIRST
    ([APPLY_NORMALIZED_CASE_HELPER_TAC case_abi_expr_pop_logs,
      LOG_ABI_TAC >> NO_TAC,
      rpt gen_tac >> strip_tac >>
      rename1 `eval_expr _ (TypeBuiltin _ tb _ _)` >>
      Cases_on `tb` >> gvs[] >> LOG_ABI_TAC >> NO_TAC,
      rpt gen_tac >> strip_tac >>
      ho_match_mp_tac case_stmt_append_logs >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC] @
     map APPLY_CASE_HELPER_TAC eval_case_helpers @
     map APPLY_NORMALIZED_CASE_HELPER_TAC eval_case_helpers @
     [simp[Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           log_extends_refl]]) >>
  simp[]

Theorem eval_mutual_log_extends[local]:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> log_extends st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> log_extends st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> log_extends st st') /\
  (!cx ty nm body vs st res st'. eval_for cx ty nm body vs st = (res,st') ==> log_extends st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> log_extends st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> log_extends st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> log_extends st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> log_extends st st') /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==> log_extends st st') /\
  (!cx e st res st'. eval_abi_expr cx e st = (res,st') ==> log_extends st st') /\
  (!cx es st res st'. eval_abi_exprs cx es st = (res,st') ==> log_extends st st')
Proof
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
    (SPECL
      [``\cx s. !st res st'. eval_stmt cx s st = (res,st') ==>
           log_extends st st'``,
       ``\cx ss. !st res st'. eval_stmts cx ss st = (res,st') ==>
           log_extends st st'``,
       ``\cx it. !st res st'. eval_iterator cx it st = (res,st') ==>
           log_extends st st'``,
       ``\cx tyv nm body vs. !st res st'.
           eval_for cx tyv nm body vs st = (res,st') ==> log_extends st st'``,
       ``\cx e. !st res st'. eval_expr cx e st = (res,st') ==>
           log_extends st st'``,
       ``\cx es. !st res st'. eval_exprs cx es st = (res,st') ==>
           log_extends st st'``,
       ``\cx t. !st res st'. eval_base_place cx t st = (res,st') ==> log_extends st st'``,
       ``\cx t. !st res st'. eval_target_place cx t st = (res,st') ==> log_extends st st'``,
       ``\cx g v. !st res st'. assign_tuple_targets cx g v st = (res,st') ==> log_extends st st'``,
       ``\cx gs vs. !st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> log_extends st st'``,
       ``\cx es. !st res st'. eval_expr_results cx es st = (res,st') ==> log_extends st st'``,
       ``\cx e. !st res st'. eval_abi_expr cx e st = (res,st') ==> log_extends st st'``,
       ``\cx es. !st res st'. eval_abi_exprs cx es st = (res,st') ==> log_extends st st'``]
      vyperInterpreterTheory.evaluate_ind)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (simp[] >> NO_TAC) >~
       [`_ ==> !st res st'.
           eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) st = (res,st') ==>
           log_extends st st'`] >-
         (rpt gen_tac >> strip_tac >> ho_match_mp_tac case_expr_ext_call_logs >>
          rpt conj_tac >> metis_tac[]) >~
       [`_ ==> !st res st'.
           eval_expr _ (Call _ (IntCall _) _ _) st = (res,st') ==>
           log_extends st st'`] >-
         (rpt gen_tac >> strip_tac >>
          RULE_ASSUM_TAC (SIMP_RULE (srw_ss())
            [type_check_def, assert_def,
             get_scopes_def, set_scopes_def, return_def, raise_def,
             push_function_def]) >>
          rewrite_tac[Once vyperInterpreterTheory.evaluate_def] >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          rpt gen_tac >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
             imp_res_tac type_check_state >> gvs[log_extends_refl]) >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
             imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
             imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          BasicProvers.LET_ELIM_TAC >>
          qpat_x_assum `_ = _` mp_tac >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
             imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          imp_res_tac type_check_state >>
          imp_res_tac lift_option_type_state >>
          gvs[type_check_def, assert_def, return_def, raise_def] >>
          unabbrev_all_tac >> gvs[arithmeticTheory.ADD_COMM] >>
          `!s0 res s1. eval_expr_results cx es s0 = (res,s1) ==>
            log_extends s0 s1` by
            (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
          BasicProvers.TOP_CASE_TAC >>
          `log_extends r r''` by (first_x_assum drule_all >> simp[]) >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[]) >>
          qmatch_asmsub_rename_tac `eval_expr_results cx es r = (INL captured,after_capture)` >>
          qmatch_goalsub_abbrev_tac `eval_exprs cxd defaults` >>
          `!s0 res s1. eval_exprs cxd defaults s0 = (res,s1) ==>
            log_extends s0 s1` by
            (rpt strip_tac >> unabbrev_all_tac >>
             PRED_ASSUM is_guarded_eval_exprs_ih drule_all >> simp[]) >>
          simp_tac std_ss [bind_def, get_scopes_def, return_def] >>
          BasicProvers.TOP_CASE_TAC >> gvs[] >>
          BasicProvers.TOP_CASE_TAC >>
          qmatch_asmsub_rename_tac `finally _ _ after_capture = (default_res,after_defaults)` >>
          `log_extends after_capture after_defaults` by
            (drule intcall_defaults_exact_log_extends >>
             disch_then irule >> first_assum MATCH_ACCEPT_TAC) >>
          `log_extends r after_capture` by
            (qpat_x_assum `!s0 res s1. eval_expr_results _ _ _ = _ ==> _` drule >> simp[]) >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[] >> metis_tac[log_extends_trans]) >>
          BasicProvers.TOP_CASE_TAC >>
          imp_res_tac read_results_state >> gvs[] >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[] >> metis_tac[log_extends_trans]) >>
          BasicProvers.TOP_CASE_TAC >>
          imp_res_tac lift_option_type_state >> gvs[] >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[] >> metis_tac[log_extends_trans]) >>
          BasicProvers.TOP_CASE_TAC >>
          imp_res_tac lift_option_type_state >> gvs[] >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[] >> metis_tac[log_extends_trans]) >>
          qmatch_goalsub_abbrev_tac `lock after_defaults` >>
          `!s0 res s1. lock s0 = (res,s1) ==> log_extends s0 s1` by
            (simp[Abbr `lock`] >> IF_CASES_TAC >>
             simp[return_def, log_extends_refl] >>
             Cases_on `cx.nonreentrant_slot` >>
             simp[raise_def, log_extends_refl] >>
             rpt strip_tac >> drule acquire_nonreentrant_lock_log_extends >> simp[]) >>
          BasicProvers.TOP_CASE_TAC >>
          qmatch_asmsub_rename_tac `lock after_defaults = (lock_res,after_lock)` >>
          `log_extends after_defaults after_lock` by
            (qpat_x_assum `!s0 res s1. lock _ = _ ==> _` drule >> simp[]) >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> gvs[] >> metis_tac[log_extends_trans]) >>
          qmatch_asmsub_rename_tac `lock after_defaults = (INL lock_value,after_lock)` >>
          Cases_on `lock_value` >>
          qmatch_asmsub_rename_tac
            `lift_option_type (lookup_callable_function _ _ _) _ _ = (INL callable,_)` >>
          `!s0 res s1. eval_stmts cxd (SND (SND (SND (SND (SND callable))))) s0 = (res,s1) ==>
            log_extends s0 s1` by
            (rpt strip_tac >> unabbrev_all_tac >>
             `LENGTH (FST (SND (SND (SND callable)))) -
                (LENGTH (FST (SND (SND callable))) - LENGTH es) =
              LENGTH es + LENGTH (FST (SND (SND (SND callable)))) -
                LENGTH (FST (SND (SND callable)))` by decide_tac >>
             pop_assum (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
             PRED_ASSUM is_guarded_eval_stmts_ih
               (drule_all o REWRITE_RULE [ignore_bind_def, GSYM CONJ_ASSOC]) >> simp[]) >>
          PRED_ASSUM is_guarded_eval_stmts_ih kall_tac >>
          PRED_ASSUM is_guarded_eval_exprs_ih kall_tac >>
          simp[push_function_def, return_def] >>
          BasicProvers.TOP_CASE_TAC >>
          qmatch_asmsub_rename_tac `finally _ _ _ = (body_res,after_body)` >>
          `log_extends (after_lock with scopes := [x'⁴']) after_body` by
            (drule intcall_body_finally_exact_log_extends >>
             disch_then irule >> simp[Abbr `cxd`]) >>
          Cases_on `body_res` >> simp[] >>
          rpt BasicProvers.TOP_CASE_TAC >>
          rpt strip_tac >> imp_res_tac lift_option_type_state >> gvs[] >>
          `log_extends r after_capture` by
            (qpat_x_assum `!s0 res s1. eval_expr_results _ _ _ = _ ==> _` drule >> simp[]) >>
          `log_extends after_defaults after_lock` by
            (qpat_x_assum `!s0 res s1. lock _ = _ ==> _` drule >> simp[]) >>
          `log_extends after_lock after_body` by
            (qpat_x_assum `log_extends (_ with scopes := _) _` mp_tac >>
             simp[log_extends_def]) >>
          rpt (qpat_x_assum `!x. _` kall_tac) >>
          metis_tac[log_extends_trans]) >~
       [`_ ==> !st res st'.
           eval_expr _ (Call _ (CreateTarget _ _ _) _ _) st = (res,st') ==>
           log_extends st st'`] >-
         suspend "CreateTarget" >>
     all_tac >>~- ([`_ ==> !st res st'.
       eval_stmt _ (Assign _ _) st = (res,st') ==> log_extends st st'`],
       PLACE_LOG_CASE_TAC) >>~-
     ([`_ ==> !st res st'.
       eval_stmt _ (AugAssign _ _ _ _) st = (res,st') ==> log_extends st st'`],
       PLACE_LOG_CASE_TAC) >>~-
     ([`!st res st'. eval_base_place _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>~-
     ([`_ ==> !st res st'. eval_base_place _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>~-
     ([`_ ==> !st res st'. eval_target_place _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>~-
     ([`!st res st'. assign_tuple_target_list _ _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>~-
     ([`_ ==> !st res st'. assign_tuple_targets _ _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>~-
     ([`_ ==> !st res st'. assign_tuple_target_list _ _ _ st = (res,st') ==>
       log_extends st st'`], PLACE_LOG_CASE_TAC) >>
     (* Keep helper dispatch separate from generic ABI traversal. *)
     TRY (FIRST (map APPLY_CASE_HELPER_TAC eval_case_helpers)) >>
     TRY (FIRST (map APPLY_NORMALIZED_CASE_HELPER_TAC eval_case_helpers)) >>
     REST_ATOMIC_DISPATCH_TAC) >>
  strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Resume eval_mutual_log_extends[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once vyperInterpreterTheory.evaluate_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  res_tac >>
  imp_res_tac eval_create_logs_extend >>
  metis_tac[log_extends_refl, log_extends_trans, log_extends_def]
QED

Finalise eval_mutual_log_extends

Theorem eval_expr_results_log_extends:
  eval_expr_results cx es st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_stmt_log_extends:
  !cx s st res st'.
    eval_stmt cx s st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_expr_log_extends:
  !cx e st res st'.
    eval_expr cx e st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_exprs_log_extends:
  !cx es st res st'.
    eval_exprs cx es st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_stmts_log_extends:
  !cx ss st res st'.
    eval_stmts cx ss st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Definition machine_log_extends_def:
  machine_log_extends (am:abstract_machine) (am':abstract_machine) <=>
    isPREFIX am.logs am'.logs
End

Theorem machine_log_extends_refl:
  machine_log_extends am am
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem machine_log_extends_trans:
  machine_log_extends am am1 /\ machine_log_extends am1 am2 ==>
  machine_log_extends am am2
Proof
  simp[machine_log_extends_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem machine_log_extends_eq_logs:
  am.logs = am'.logs ==> machine_log_extends am am'
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem abstract_machine_from_state_logs[simp]:
  (abstract_machine_from_state srcs exps layouts st).logs = st.logs
Proof
  simp[vyperInterpreterTheory.abstract_machine_from_state_def]
QED

Theorem merge_constants_logs[local]:
  (merge_constants addr src_id_opt cenv am).logs = am.logs
Proof
  simp[vyperInterpreterTheory.merge_constants_def]
QED

Theorem evaluate_all_constants_logs:
  evaluate_all_constants cx am addr mods = SOME am' ==> am'.logs = am.logs
Proof
  simp[vyperInterpreterTheory.evaluate_all_constants_def] >>
  qid_spec_tac `am` >>
  qspec_tac (`constants_order mods`, `mods`) >> Induct >-
    simp[vyperInterpreterTheory.evaluate_module_constants_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[vyperInterpreterTheory.evaluate_module_constants_def, AllCaseEqs()] >>
  rpt strip_tac >>
  first_x_assum drule >>
  simp[merge_constants_logs]
QED

Theorem acquire_nonreentrant_lock_logs[local]:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.acquire_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `lookup_storage (n2w slot)
              (vfmExecution$lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  gvs[vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem release_nonreentrant_lock_logs[local]:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.release_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem send_call_value_logs[local]:
  send_call_value mut cx st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.send_call_value_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  imp_res_tac transfer_value_logs >> gvs[]
QED

Theorem entry_lock_action_logs[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot =>
         acquire_nonreentrant_lock cx.txn.target slot is_view
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  metis_tac[acquire_nonreentrant_lock_logs]
QED

Theorem exit_unlock_action_logs[local]:
  (if nr /\ ~is_view then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `is_view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.return_def] >>
  metis_tac[release_nonreentrant_lock_logs]
QED

Theorem external_unlock_action_logs[local]:
  (if nr /\ mut <> View /\ mut <> Pure then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `mut = View` >> Cases_on `mut = Pure` >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[vyperStateTheory.return_def] >>
  metis_tac[release_nonreentrant_lock_logs]
QED

Theorem call_body_pipeline_log_extends[local]:
  (do lock_action; send_call_value mut cx; eval_stmts cx body od) st =
    (res,st') ==>
  (!s0 r s1. lock_action s0 = (r,s1) ==> s1.logs = s0.logs) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do lock_action; send_call_value _ _; eval_stmts _ _ od) _ = _`
    mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac send_call_value_logs >>
  imp_res_tac eval_stmts_log_extends >>
  metis_tac[log_extends_eq_logs, log_extends_trans]
QED
Theorem call_external_function_success_log_extends:
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_log_extends am am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.call_external_function_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `(do
               if nr then
                 case cx.nonreentrant_slot of
                   NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot =>
                     acquire_nonreentrant_lock cx.txn.target slot
                       (mut = View \/ mut = Pure)
               else return ();
               send_call_value mut cx;
               eval_stmts cx body
             od) (initial_state am_c [env] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q` >> gvs[AllCaseEqs()] >>
  Cases_on `(if nr /\ mut <> View /\ mut <> Pure then
               case cx.nonreentrant_slot of
                 NONE => return ()
               | SOME slot =>
                   release_nonreentrant_lock cx.txn.target slot
             else return ()) r` >>
  Cases_on `q` >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `y` >> gvs[AllCaseEqs()]) >>
  TRY (Cases_on `evaluate_type (type_env_all_modules all_mods) ret` >>
       gvs[AllCaseEqs()]) >>
  TRY (Cases_on `safe_cast x v'` >> gvs[AllCaseEqs()]) >>
  drule call_body_pipeline_log_extends >>
  (impl_tac >-
     (rpt strip_tac >> imp_res_tac entry_lock_action_logs)) >>
  strip_tac >>
  imp_res_tac external_unlock_action_logs >>
  imp_res_tac evaluate_all_constants_logs >>
  gvs[machine_log_extends_def, log_extends_def]
QED

Theorem call_external_success_log_extends:
  call_external orc am tx = (INL v,am',rqs) ==> machine_log_extends am am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.call_external_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac call_external_function_success_log_extends >>
  gvs[machine_log_extends_def, vyperInterpreterTheory.finalize_pending_deletions_def]
QED

Theorem call_external_function_error_logs_rollback:
  call_external_function orc am cx nr mut ts all_mods args dflts vals body ret =
    (INR e,am',rqs) ==>
  am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_function_error_rollback >> gvs[]
QED

Theorem call_external_error_logs_rollback:
  call_external orc am tx = (INR e,am',rqs) ==> am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_error_rollback >> gvs[]
QED

Theorem call_external_log_extends:
  call_external orc am tx = (res,am',rqs) ==> machine_log_extends am am'
Proof
  Cases_on `res` >> strip_tac >-
    (imp_res_tac call_external_success_log_extends) >>
  imp_res_tac call_external_error_logs_rollback >>
  simp[machine_log_extends_eq_logs]
QED

Theorem call_external_transaction_log_extends_empty:
  call_external_transaction orc am tx = (res,am',rqs) ==>
  isPREFIX [] am'.logs
Proof
  simp[]
QED

Theorem call_external_transaction_success_fresh:
  call_external_transaction orc am tx = (INL v,am',rqs) ==>
  call_external orc (clear_machine_logs am) tx = (INL v,am',rqs) /\
  machine_log_extends (clear_machine_logs am) am'
Proof
  simp[vyperInterpreterTheory.call_external_transaction_def] >>
  metis_tac[call_external_log_extends]
QED

(* Integration audit: all log preservation exports must be kernel closed. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Log preservation oracle debt: " ^ name)
  end) (DB.thms "vyperLogPreservation");
