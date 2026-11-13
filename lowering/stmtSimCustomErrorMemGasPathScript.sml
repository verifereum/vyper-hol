(* Replay-aware composition of custom-error arguments and the revert tail. *)
Theory stmtSimCustomErrorMemGasPath
Ancestors
  stmtSimCustomErrorSourcePath gasOutcome gasSummary gasSummaryCompose
  gasContext gasExemptCert fragGasPathMem fragGasMode stmtSimDefs
  vyperInterpreter vyperState list exprSimDefs
Libs
  monadsyntax

Theorem custom_error_args_revert_outcome_mem:
  get_module_code cx (FST id) = SOME tops /\
  lookup_custom_error_args_in (SND id) tops = SOME params /\
  order_custom_error_args params (CustomError id positional kwargs) = SOME args /\
  gas_admissible
    (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
    (stmt_res_ok lctx) es /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0) Q
    (\res ee exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit) /\
  (!marks res mid r.
    gas_marked_exec T (ctx,func) (eval_exprs cx args) (es,s0) marks res mid (OK r) /\
    Q res (mid with gas_obs := []) r ==>
    ?vs t. res = INL vs /\ gas_path_mem ctx func r 0 (Abort Revert_abort t)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_stmt cx (Raise (RaiseCustomError (CustomError id positional kwargs))))
    (es,s0) (\res ee r. F)
    (\res ee exit. stmt_res_ok lctx res /\ stmt_exit RetQ ee res exit)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (fs[gas_summary_at_def]
      >- (gvs[] >> first_x_assum drule_all >> strip_tac >> gvs[] >>
          drule_all eval_raise_custom_error_bind >> disch_tac >>
          qexists_tac `marks` >> disj1_tac >>
          Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs` >>
          gvs[gas_marked_exec_def] >>
          simp[bind_def, lift_option_def, raise_def, return_def,
               stmt_res_ok_def, stmt_exit_def, expr_exit_def] >>
          qrefinel [`_`,`es_end`,`Abort Revert_abort t'`] >>
          simp[expr_exit_def, fragExecTheory.exit_result_def] >>
          drule (Q.INST [`memory` |-> `T`] gas_marked_path_from_mem) >>
          disch_tac >> drule_all gas_marked_path_then >> simp[]) >>
      gvs[] >> drule_all eval_raise_custom_error_bind >> disch_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`,`es_end`,`exit`] >>
      simp[] >>
      conj_tac
      >- (asm_rewrite_tac[] >> irule gas_marked_exec_bind_exception >> simp[]) >>
      conj_tac
      >- (gvs[gas_admissible_def, gas_marked_exec_def] >>
          qpat_x_assum `!gs res es'. _` (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
          qpat_assum `!tail. eval_exprs _ _ _ = _` (mp_tac o Q.SPEC `[]`) >>
          pure_rewrite_tac [APPEND_NIL] >> disch_tac >> simp[bind_def]) >>
      metis_tac[custom_error_argument_exception_exit]) >>
  qexists_tac `marks` >> disj2_tac >>
  drule_all raise_custom_error_args_exempt >>
  metis_tac[]
QED
