(* Counted expression evaluation followed by an internal return suffix. *)
Theory internalReturnComposeMem
Ancestors
  stmtSimDefs exprSimMemDefs stmtSimReturn returnValueTyped
  gasSummary gasSummaryCompose gasContext fragGasMode fragGasPathMem fragGasPath
  exprSimDefs exprSimProps stmtSimProps
  vyperInterpreter vyperState venomState

Theorem internal_return_value_summary_mem:
  gas_summary_at T (ctx,func) marks
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!ee v t. P v ee t /\
    (?gs ee'. bind (eval_expr cx e) (read_result cx)
                (es with gas_obs := gs) = (INL v, ee')) /\ ~t.vs_halted ==>
    ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
      !tail. RetQ v ((ee with gas_obs := tail) with scopes := []) r) ==>
  !Q. ?marks'. gas_summary_at T (ctx,func) marks'
    (eval_stmt cx (Return (SOME e))) (es,s0) Q
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> gen_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `~t.vs_halted` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >>
         metis_tac[gas_marked_path_exec, gas_path_normal]) >>
      drule marked_exec_source_eq >> strip_tac >>
      first_x_assum drule >> simp[] >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexists_tac `marks ++ REPLICATE n F` >>
      qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
      reverse conj_tac
      >- (simp[stmt_exit_def] >> metis_tac[]) >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `v`] >>
      simp[gas_marked_exec_def, gas_marked_path_def, raise_def]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  qexists_tac `marks` >> qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED
