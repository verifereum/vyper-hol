(* Source-only boundaries for the shared custom-error path. *)
Theory stmtSimCustomErrorSourcePath
Ancestors
  stmtSimDefs gasContext gasExemptCert vyperInterpreter vyperState
  vyperValue exprSimDefs
Libs
  monadsyntax

Theorem eval_raise_custom_error_bind:
  get_module_code cx (FST id) = SOME tops /\
  lookup_custom_error_args_in (SND id) tops = SOME params /\
  order_custom_error_args params (CustomError id positional kwargs) = SOME args ==>
  eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))) =
  bind (eval_exprs cx args)
    (\vs. do data <- lift_option
       (build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs)
       "custom error encoding";
       raise $ Error (RevertData data) od)
Proof
  strip_tac >> simp[Once evaluate_def]
QED

Theorem custom_error_continuation_result:
  ?err. (do data <- lift_option
      (build_custom_error_data tenv name tys vs) "custom error encoding";
      (raise (vyperState$Error (RevertData data)) : evaluation_state -> unit evaluation_result)
    od) ee = (INR (Error err) : unit + exception,ee) /\
    ((?m. err = RuntimeError m) \/ (?d. err = RevertData d))
Proof
  Cases_on `build_custom_error_data tenv name tys vs` >>
  simp[lift_option_def, bind_def, raise_def, return_def]
QED

Theorem custom_error_continuation_exit:
  !tail. ?res.
    (do data <- lift_option
      (build_custom_error_data tenv name tys vs) "custom error encoding";
      (raise (vyperState$Error (RevertData data)) : evaluation_state -> unit evaluation_result)
    od) (ee with gas_obs := tail) = (res,ee with gas_obs := tail) /\
    stmt_res_ok lctx res /\ stmt_exit RetQ ee res (Abort Revert_abort t)
Proof
  gen_tac >> Cases_on `build_custom_error_data tenv name tys vs` >>
  simp[lift_option_def, bind_def, raise_def, return_def,
       stmt_res_ok_def, stmt_exit_def, expr_exit_def]
QED

Theorem custom_error_argument_exception_exit:
  expr_exit (INR ex : eval_result + exception) exit ==>
  stmt_exit RetQ ee (INR ex) exit
Proof
  Cases_on `exit` >> Cases_on `ex` >>
  simp[expr_exit_def, stmt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem raise_custom_error_args_admissible:
  get_module_code cx (FST id) = SOME tops /\
  lookup_custom_error_args_in (SND id) tops = SOME params /\
  order_custom_error_args params (CustomError id positional kwargs) = SOME args /\
  gas_admissible
    (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
    (stmt_res_ok lctx) es ==>
  gas_admissible (ignore_bind (eval_exprs cx args) (return ()))
    (stmt_res_ok lctx) es
Proof
  strip_tac >> drule_all eval_raise_custom_error_bind >> strip_tac >>
  simp[gas_admissible_def] >> rpt gen_tac >>
  Cases_on `eval_exprs cx args (es with gas_obs := gs)` >>
  rename1 `_ = (result,mid)` >> Cases_on `result`
  >- simp[ignore_bind_def, bind_def, return_def, stmt_res_ok_def] >>
  simp[ignore_bind_def, bind_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[bind_def]
QED

Theorem raise_custom_error_args_exempt:
  get_module_code cx (FST id) = SOME tops /\
  lookup_custom_error_args_in (SND id) tops = SOME params /\
  order_custom_error_args params (CustomError id positional kwargs) = SOME args /\
  gas_exempt_cert memory source_tops (ctx,func)
    (ignore_bind (eval_exprs cx args) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory source_tops (ctx,func)
    (ignore_bind
      (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
      (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  strip_tac >> drule_all eval_raise_custom_error_bind >> strip_tac >>
  asm_rewrite_tac[] >>
  `ignore_bind
    (bind (eval_exprs cx args)
      (\vs. do data <- lift_option
        (build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs)
        "custom error encoding";
        (raise (vyperState$Error (RevertData data)) : evaluation_state -> unit evaluation_result) od)) (return ()) =
   bind (eval_exprs cx args)
      (\vs. ignore_bind
        (do data <- lift_option
          (build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs)
          "custom error encoding";
          (raise (Error (RevertData data)) : evaluation_state -> unit evaluation_result)
         od) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_exprs cx args x` >>
     rename1 `_ = (result,mid)` >> Cases_on `result` >> simp[bind_def]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_values >> simp[]
QED
