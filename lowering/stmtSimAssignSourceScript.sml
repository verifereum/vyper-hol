(* Admissible source-action boundaries for assignment to a local. *)
Theory stmtSimAssignSource
Ancestors
  stmtSimDefs exprSimDefs gasContext gasExemptCert stmtSimAssignStore
  vyperInterpreter vyperState vyperExprNoControl
Libs
  monadsyntax

Theorem assign_local_admissible_run:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es ==>
  !gs. eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)
      (es with gas_obs := gs) =
    bind (bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [])) (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `eval_expr cx e (es with gas_obs := gs) = (rr, ee)` >>
  Cases_on `rr` >> simp[] >>
  Cases_on `read_result cx x ee` >>
  rename1 `read_result cx x ee = (rr2, ee')` >>
  imp_res_tac read_result_state >> gvs[] >>
  Cases_on `rr2` >> simp[] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def] >>
  Cases_on `lookup_scopes id ee.scopes` >>
  simp[raise_def, return_def, get_place_def, stmt_res_ok_def]
QED

Theorem assign_local_admissible_rhs:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control]
     >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`, `gs`] >>
     drule assign_local_admissible_run >>
     disch_then (qspec_then `gs` SUBST1_TAC) >>
     simp[Once bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assign_local_continuation_success:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  ?pre env entry rest.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.assignable /\
    write_place cx (MemoryPlace id []) v ee =
      (INL (), ee with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
Proof
  strip_tac >>
  `stmt_res_ok lctx (FST (write_place cx (MemoryPlace id []) v ee))` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`SND (write_place cx (MemoryPlace id []) v ee)`, `gs`] >>
     drule assign_local_admissible_run >>
     disch_then (qspec_then `gs` SUBST1_TAC) >>
     simp[Once bind_def]) >>
  Cases_on `write_place cx (MemoryPlace id []) v ee` >>
  drule write_place_local >>
  impl_tac >- gvs[stmt_res_ok_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem write_place_local_success_gas_obs:
  write_place cx (MemoryPlace id []) v ee = (INL (), ee') ==>
  !tail. write_place cx (MemoryPlace id []) v (ee with gas_obs := tail) =
    (INL (), ee' with gas_obs := tail)
Proof
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id ee.scopes` >>
  simp[raise_def, return_def] >>
  rename1 `SOME q` >> PairCases_on `q` >> Cases_on `q2.assignable` >>
  gvs[assert_def, ignore_bind_def, bind_def, return_def, raise_def,
      set_scopes_def] >> strip_tac >> gvs[]
QED

Theorem assign_local_continuation_all_tails:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := prefix ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env entry rest.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.assignable /\
    !tail. write_place cx (MemoryPlace id []) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
  drule_all assign_local_continuation_success >> strip_tac >>
  qexistsl [`pre`, `env`, `entry`, `rest`] >> gvs[] >>
  drule write_place_local_success_gas_obs >> simp[]
QED

Theorem assign_local_exempt:
  (!memory tops ctx' func' cx' e' es' s0 marks err ee leaf fin.
     gas_exempt_cert memory tops (ctx', func')
       (ignore_bind (bind (eval_expr cx' e') (read_result cx')) (return ()))
       (es', s0) marks (err, ee) (leaf, fin) ==>
     gas_exempt_cert memory tops (ctx', func')
       (ignore_bind (eval_expr cx' e') (return ()))
       (es', s0) marks (err, ee) (leaf, fin)) /\
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es, s0) marks (err, ee) (leaf, fin) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (return ()))
    (es, s0) marks (err, ee) (leaf, fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind
       (bind (eval_target_place cx (NameTarget id))
         (\p. write_place cx p v)) (return ()))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_value >> simp[]
QED
