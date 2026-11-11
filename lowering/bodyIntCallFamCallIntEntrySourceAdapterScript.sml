(* Source continuation transport after the actual argument-list run. *)
Theory bodyIntCallFamCallIntEntrySourceAdapter
Ancestors
  bodyIntCallFamCallIntEntrySource exprExtRequestSuffix exprExtRequestReadProbe
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode
  vyperStatePreservation vyperInterpreter vyperState exprSimDefs
Libs
  monadsyntax

Theorem intcall_read_results_no_exempt_error:
  !rs cx st err st'.
    read_results cx rs st = (INR (Error err),st') ==>
    ~unspecified_behaviour_exempt tops err
Proof
  Induct >> simp[read_results_def, return_def] >>
  rpt gen_tac >>
  Cases_on `read_result cx h st` >> rename1 `read_result cx h st = (rr,mid)` >>
  Cases_on `rr` >> simp[bind_def, return_def]
  >- (Cases_on `read_results cx rs mid` >>
      rename1 `read_results cx rs mid = (rr,fin)` >>
      Cases_on `rr` >> simp[bind_def, return_def] >> metis_tac[]) >>
  metis_tac[read_result_no_exempt_error]
QED

Theorem intcall_outcome_get_scopes:
  gas_outcome memory tops (ctx,func) (k es.scopes) (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) (bind get_scopes k) (es,s) Q R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_at_def, gas_marked_exec_def, get_scopes_def, bind_def,
          return_def] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  gvs[ignore_bind_def]
QED

Theorem intcall_outcome_push_function:
  ~s.vs_halted /\
  gas_outcome memory tops (ctx,func) rest
    (es with <|scopes := [penv]; gas_obs := []|>,s) Q R ==>
  gas_outcome memory tops (ctx,func)
    (ignore_bind (push_function src penv cx) rest)
    (es with gas_obs := [],s) Q R
Proof
  strip_tac >>
  `ignore_bind (push_function src penv cx) rest =
   ignore_bind (set_scopes [penv]) rest` by
    simp[FUN_EQ_THM, ignore_bind_def, bind_def, push_function_def,
         set_scopes_def, return_def] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_at_def, gas_marked_exec_def, set_scopes_def,
          ignore_bind_def, bind_def, return_def] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_exempt_cert_bind_unit))) >>
  qexistsl_tac [`es with scopes := [penv]`, `s`] >>
  simp[gas_marked_exec_def, set_scopes_def, return_def,
       fragGasModeTheory.gas_marked_path_def, ignore_bind_def] >>
  conj_tac >- gvs[ignore_bind_def] >>
  Cases_on `memory` >> simp[] >>
  metis_tac[fragGasPathMemTheory.gas_path_mem_rules,
            fragGasPathTheory.gas_path_rules]
QED

Theorem intcall_outcome_read_results:
  ~s.vs_halted /\
  (!tail. read_results cx results (es with gas_obs := tail) =
    (INL vs,es with gas_obs := tail)) /\
  gas_outcome memory tops (ctx,func) (k vs)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome memory tops (ctx,func) (bind (read_results cx results) k)
    (es with gas_obs := [],s) Q R
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_at_def, gas_marked_exec_def, bind_def] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`]
    (SPEC_ALL gas_exempt_cert_bind_values))) >>
  qexistsl_tac [`es`, `s`, `vs`] >>
  simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  conj_tac >- gvs[ignore_bind_def] >>
  Cases_on `memory` >> simp[] >>
  metis_tac[fragGasPathMemTheory.gas_path_mem_rules,
            fragGasPathTheory.gas_path_rules]
QED

Theorem intcall_outcome_read_error:
  (!tail. read_results cx results (es with gas_obs := tail) =
    (INR ex,es with gas_obs := tail)) /\
  gas_outcome memory tops (ctx,func) (raise ex)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome memory tops (ctx,func) (bind (read_results cx results) k)
    (es with gas_obs := [],s) Q R
Proof
  strip_tac >>
  `!tail. bind (read_results cx results) k (es with gas_obs := tail) =
    raise ex (es with gas_obs := tail)` by simp[bind_def, raise_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      fs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, raise_def] >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  metis_tac[intcall_read_results_no_exempt_error]
QED

Theorem intcall_source_read_bind_outcome:
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,F,args,[],ret,ss) /\ LENGTH es = LENGTH args /\
  gas_admissible (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
    expr_vv_res_ok start /\
  gas_marked_exec F (ctx,func) (eval_expr_results cx es)
    (start,s0) marks (INL results) mid (OK t) /\ ~t.vs_halted /\
  (!vs penv rtv.
    read_results cx results (mid with gas_obs := []) =
      (INL vs,mid with gas_obs := []) /\
    bind_arguments (get_tenv cx) args vs = SOME penv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    gas_admissible (intcall_rest cx name mut ss mid.scopes rtv)
      expr_vv_res_ok (mid with <|scopes := [penv]; gas_obs := []|>) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (intcall_rest cx name mut ss mid.scopes rtv)
      (mid with <|scopes := [penv]; gas_obs := []|>,t) Q R) /\
  (!ex. read_results cx results (mid with gas_obs := []) =
    (INR ex,mid with gas_obs := []) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (raise ex)
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do prev <- get_scopes;
        vs <- read_results cx results;
        penv <- lift_option_type (bind_arguments (get_tenv cx) args vs)
          "IntCall bind_arguments";
        rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
        push_function (NONE,name) penv cx;
        intcall_rest cx name mut ss prev rtv od)
    (mid with gas_obs := [],t) Q R
Proof
  strip_tac >>
  `!tail. read_results cx results (mid with gas_obs := tail) =
    (FST (read_results cx results mid),mid with gas_obs := tail)` by
    (gen_tac >> irule extrequest_read_results_frame >>
     simp[extrequest_read_frame_def]) >>
  irule intcall_outcome_get_scopes >> simp[] >>
  Cases_on `FST (read_results cx results mid)`
  >- (rename1 `FST (read_results cx results mid) = INL vs` >>
      fs[gas_marked_exec_def] >>
      qpat_assum `!tail. eval_expr_results _ _ _ = _`
        (qspec_then `[]` assume_tac) >>
      qpat_assum `!tail. read_results _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule_all intcall_source_bind_types >> strip_tac >>
      irule intcall_outcome_read_results >> simp[] >>
      simp[lift_option_type_def, bind_return] >>
      irule intcall_outcome_push_function >> simp[] >>
      first_x_assum irule >> simp[] >>
      irule intcall_source_rest_admissible >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `FST (read_results cx results mid) = INR ex` >>
  irule intcall_outcome_read_error >> qexists_tac `ex` >> simp[]
QED
