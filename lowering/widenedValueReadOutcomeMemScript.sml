(* Preserve physical value layout while forcing a source result. *)
Theory widenedValueReadOutcomeMem
Ancestors
  exprSimMemorySource exprSimMemDefs gasOutcome gasSummary gasSummaryCompose
  exprSimDefs exprSimProps exprSimUnwrapProps vyperState
Libs monadsyntax

Theorem value_read_outcome_mem:
  gas_outcome T tops (ctx,func) (eval_expr cx e) (es,s0)
    P (\res ee r. expr_exit res r) /\
  (!res ee t. P res ee t ==>
    ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee)) ==>
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?raw v. res = INL v /\ P (INL raw) ee t /\
       read_result cx raw ee = (INL v,ee))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- (gvs[] >> first_x_assum drule >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t`] >>
          simp[] >> conj_tac
          >- (drule read_result_gas_obs >> strip_tac >>
              gvs[gas_marked_exec_def, bind_def]) >>
          metis_tac[]) >>
      simp[gas_summary_at_def] >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def] >>
      rename1 `expr_exit (INR (Error err)) _` >>
      Cases_on `err` >> gvs[expr_exit_def]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule force_exempt_cert >> simp[]
QED
