(* Replay-aware composition of custom-error arguments and the revert tail,
   for both memory modes of gas_outcome. *)
Theory stmtSimCustomErrorGasPath
Ancestors
  stmtSimCustomErrorSourcePath gasOutcome gasSummary gasSummaryCompose
  gasContext gasExemptCert gasStorage vyperStorageTrace vyperStorageFootprint
  fragGasPathMem fragGasMode stmtSimDefs
  vyperInterpreter vyperState list exprSimDefs
Libs
  monadsyntax

Theorem custom_error_args_revert_outcome:
  get_module_code cx (FST id) = SOME tops /\
  lookup_custom_error_args_in (SND id) tops = SOME params /\
  order_custom_error_args params (CustomError id positional kwargs) = SOME args /\
  gas_admissible
    (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
    (stmt_res_ok lctx) es /\
  gas_outcome memory (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0) Q
    (\H res ee exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit) /\
  (!marks res mid r.
    gas_marked_exec memory (ctx,func) (eval_exprs cx args) (es,s0) marks res mid (OK r) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Q H res (mid with gas_obs := []) r) ==>
    ?vs t. res = INL vs /\ gas_path_mem ctx func r 0 (Abort Revert_abort t)) ==>
  gas_outcome memory (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
    (es,s0) (\H res ee r. F)
    (\H res ee exit. stmt_res_ok lctx res /\ stmt_exit (RetQ H) ee res exit)
Proof
  strip_tac >>
  `!vs. storage_trace_frame
     (\ee. (do data <- lift_option
       (build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs)
       "custom error encoding";
       (raise (Error (RevertData data)) : evaluation_state -> unit evaluation_result)
       od) ee)` by
    (gen_tac >>
     Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs` >>
     simp[lift_option_def, bind_def, return_def, raise_def,
          storage_trace_frame_def]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (drule_all eval_raise_custom_error_bind >> disch_tac >>
      qexists_tac `marks` >> disj1_tac >> asm_rewrite_tac[] >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (drule_all eval_raise_custom_error_bind >> disch_tac >>
           qexists_tac `marks` >> disj1_tac >> asm_rewrite_tac[] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        metis_tac[storage_trace_domain_def]
      >- (gvs[] >> qpat_x_assum `!marks res mid r. _` drule_all >>
          strip_tac >> gvs[] >>
          drule_all eval_raise_custom_error_bind >> disch_tac >>
          qexists_tac `marks` >> disj2_tac >> disj1_tac >>
          Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs` >>
          gvs[gas_marked_exec_def] >>
          simp[bind_def, lift_option_def, raise_def, return_def,
               stmt_res_ok_def, stmt_exit_def, expr_exit_def] >>
          qrefinel [`_`,`es_end`,`Abort Revert_abort t'`] >>
          simp[expr_exit_def, fragExecTheory.exit_result_def] >>
          drule gas_marked_path_from_mem >>
          disch_then (qspec_then `memory` assume_tac) >>
          drule_all gas_marked_path_then >> simp[]) >>
      rename1 `exit_result exit` >>
      `?exc. res = INR exc /\
         expr_exit (INR exc : eval_result + exception) exit` by metis_tac[] >>
      gvs[] >> drule_all eval_raise_custom_error_bind >> disch_tac >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`,`es_end`,`exit`] >>
      simp[] >>
      conj_tac
      >- (asm_rewrite_tac[] >> irule gas_marked_exec_bind_exception >> simp[]) >>
      rpt strip_tac >>
      conj_tac
      >- (gvs[gas_admissible_def, gas_marked_exec_def] >>
          qpat_x_assum `!gs res es'. _` (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
          qpat_assum `!tail. eval_exprs _ _ _ = _` (mp_tac o Q.SPEC `[]`) >>
          pure_rewrite_tac [APPEND_NIL] >> disch_tac >> simp[bind_def]) >>
      metis_tac[custom_error_argument_exception_exit]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  drule_all raise_custom_error_args_exempt >>
  metis_tac[]
QED
