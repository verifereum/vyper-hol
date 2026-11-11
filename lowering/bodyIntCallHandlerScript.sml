(* Callee-only admissibility and exception transport boundaries. *)
Theory bodyIntCallHandler
Ancestors
  stmtSimDefs exprSimDefs gasExemptCert gasSummary gasContext vyperInterpreter vyperState
Libs
  monadsyntax

Theorem function_rest_body_admissible:
  gas_admissible
    (bind (finally
      (try (ignore_bind (a : evaluation_state -> unit evaluation_result)
        (return NoneV)) handle_function) (set_scopes saved)) k)
    expr_vv_res_ok es ==>
  gas_admissible a (stmt_res_ok NoLoop) es
Proof
  rw[gas_admissible_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> simp[stmt_res_ok_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[stmt_res_ok_def, ignore_bind_def, bind_def, try_def, finally_def,
       handle_function_def, set_scopes_def, return_def, raise_def,
       expr_vv_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  simp[stmt_res_ok_def, ignore_bind_def, bind_def, try_def, finally_def,
       handle_function_def, set_scopes_def, return_def, raise_def,
       expr_vv_res_ok_def]
QED

Theorem function_rest_handler_admissible:
  gas_admissible (bind (finally a (set_scopes saved)) k)
    expr_vv_res_ok es ==>
  gas_admissible a expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[expr_res_ok_def, bind_def, finally_def, ignore_bind_def,
       set_scopes_def, return_def, raise_def, expr_vv_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  simp[expr_res_ok_def, bind_def, finally_def, ignore_bind_def,
       set_scopes_def, return_def, raise_def, expr_vv_res_ok_def]
QED

Theorem function_body_exempt_handler:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (a : evaluation_state -> unit evaluation_result) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (try (ignore_bind a (return NoneV)) handle_function)
      (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[ignore_bind_try_unit, ignore_bind_return_twice] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_function_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem function_body_marked_handler:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> unit evaluation_result)
    (es,s0) marks res mid r /\
  (!tail. (case res of INL u => return NoneV | INR exc => handle_function exc)
    (mid with gas_obs := tail) = (out,fin with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx,func)
    (try (ignore_bind a (return NoneV)) handle_function)
    (es,s0) marks out fin r
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> Cases_on `res` >>
  gvs[try_def, ignore_bind_def, bind_def, return_def]
QED
