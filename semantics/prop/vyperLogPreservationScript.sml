Theory vyperLogPreservation

Ancestors
  vyperCall vyperStatePreservation

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

Theorem case_eval_targets_nil_logs[local]:
  eval_targets cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_eval_targets_cons_logs[local]:
  (!s0 r s1. eval_target cx g s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 gv s1. eval_target cx g s0 = (INL gv,s1) ==>
     !s2 r s3. eval_targets cx gs s2 = (r,s3) ==> log_extends s2 s3) ==>
  !st res st'. eval_targets cx (g::gs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  metis_tac[log_extends_trans]
QED

Theorem case_target_base_logs[local]:
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_target cx (BaseTarget bt) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[vyperStateTheory.return_def] >>
  first_x_assum drule >> simp[]
QED

Theorem case_target_tuple_logs[local]:
  (!s0 r s1. eval_targets cx gs s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_target cx (TupleTarget gs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def, AllCaseEqs(),
       vyperStateTheory.return_def] >>
  metis_tac[]
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
  imp_res_tac materialise_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `log_extends _ _` mp_tac >>
  simp[log_extends_def]
QED

Theorem case_iterator_range_logs[local]:
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 r s1. eval_expr cx e2 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_iterator cx (Range e1 e2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_sum_state >> gvs[] >>
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
  Cases_on `find_var_decl_by_num n ts` >>
  gvs[vyperStateTheory.raise_def] >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> gvs[]
QED


Theorem subscript_terminal_logs[local]:
  (do v2 <- get_Value tv2;
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv (expr_type e1))
                   "Subscript array type";
      check_array_bounds cx tv1 v2;
      r <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
      case r of
        INL v => return v
      | INR (is_transient,slot,tv) => do
          v <- read_storage_slot cx is_transient slot tv;
          return (Value v)
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac check_array_bounds_state >> imp_res_tac lift_sum_state >> gvs[] >>
  Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  PairCases_on `y` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_state >> imp_res_tac return_state >> gvs[]
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
      write_storage_slot cx is_transient last_slot pop_elem_tv
        (default_value pop_elem_tv);
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
          write_storage_slot cx is_transient last_slot pop_elem_tv
            (default_value pop_elem_tv);
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
  imp_res_tac get_Value_state >> imp_res_tac materialise_state >>
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
  imp_res_tac get_Value_state >> imp_res_tac type_check_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem push_scope_log_extends[local]:
  push_scope st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.push_scope_def, vyperStateTheory.return_def] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem finally_switch_BoolV_log_extends[local]:
  finally (switch_BoolV tv f g) pop_scope st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperInterpreterTheory.switch_BoolV_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> gvs[vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  TRY (irule log_extends_trans >> goal_assum drule >>
       first_assum MATCH_ACCEPT_TAC)
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
     !st res st'. eval_for cx tyv (string_to_num id) body vs st = (res,st') ==>
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
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac lift_option_type_state >> gvs[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  imp_res_tac check_state >> imp_res_tac type_check_state >> gvs[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


Theorem case_stmt_raise_logs[local]:
  (!e. reason = RaiseReason e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Raise reason) st = (res,st') ==>
    log_extends st st'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `reason` >>
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_option_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED

Theorem case_stmt_assert_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (!se. reason = AssertReason se ==>
     !s0 r s1. eval_expr cx se s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e reason) st = (res,st') ==>
    log_extends st st'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `reason` >>
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> gvs[] >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def] >>
  rpt IF_CASES_TAC >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac get_Value_state >> imp_res_tac lift_option_state >>
       imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[]) >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
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


Theorem case_base_target_name_logs[local]:
  eval_base_target cx (NameTarget id) st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl]
QED

Theorem case_base_target_toplevel_logs[local]:
  eval_base_target cx (TopLevelNameTarget sid) st = (res,st') ==>
    log_extends st st'
Proof
  PairCases_on `sid` >> strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  Cases_on `is_immutable_decl (string_to_num sid1) ts` >>
  gvs[vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_base_target_attribute_logs[local]:
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_base_target cx (AttributeTarget bt id) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[vyperStateTheory.return_def] >>
  first_x_assum drule >> simp[]
QED

Theorem case_base_target_subscript_logs[local]:
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_base_target cx (SubscriptTarget bt e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `x` >> gvs[vyperStateTheory.bind_def,
                           vyperStateTheory.return_def, AllCaseEqs()] >>
  imp_res_tac get_Value_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem switch_BoolV_log_extends[local]:
  switch_BoolV tv f g st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def] >>
  rpt IF_CASES_TAC >> simp[vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  first_x_assum drule >> simp[]
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
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `!sb rb sb'. eval_expr cx e2 sb = (rb,sb') ==> log_extends sb sb'` by
    (qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e2 _ = _ ==> _`
       drule >> simp[]) >>
  `!sb rb sb'. eval_expr cx e3 sb = (rb,sb') ==> log_extends sb sb'` by
    (qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e3 _ = _ ==> _`
       drule >> simp[]) >>
  `log_extends s'' st'` by
    (drule switch_BoolV_log_extends >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `log_extends st s''` by
    (qpat_x_assum `!s0 r s1. eval_expr _ e1 _ = _ ==> _` drule >> simp[]) >>
  irule log_extends_trans >> qexists_tac `s''` >> simp[]
QED

Theorem case_expr_struct_lit_logs[local]:
  (!s0 r s1. eval_exprs cx (MAP SND kes) s0 = (r,s1) ==>
     log_extends s0 s1) ==>
  !st res st'. eval_expr cx (StructLit ty sid kes) st = (res,st') ==>
    log_extends st st'
Proof
  PairCases_on `sid` >> rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
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
  imp_res_tac get_Value_state >> imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_expr_type_builtin_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (TypeBuiltin ty tb typ es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_state >> imp_res_tac lift_sum_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED


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
     materialise cx tv s2 = (INL v,s3) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_exprs cx (e::es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac materialise_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


val _ = export_theory();
