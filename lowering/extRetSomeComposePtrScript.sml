Theory extRetSomeComposePtr
Ancestors
  bodyPtrDefs gasSummaryComposePtr gasExemptCert
  stmtSimProps stmtSimReturn exprSimDefs fragExec fragGasPathPtr gasSummary vyperInterpreter vyperState

Theorem external_return_some_outcome_ptr:
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P
    (\res ee gt r. expr_exit res r) /\
  (!res ee G1 tn1 t. P res ee G1 tn1 t ==>
    ?v G2 tn2 u. res = INL v /\
      gas_path_ptr (cx_dead cx) 0 ctx func PG G1 tn1 t 0 G2 tn2 (Halt u)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (Return (SOME e))) (es,s,G,tn) Q
    (\res ee gt r. !tail.
      stmt_exit_ptr (\v es gt r. T) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_outcome_ptr_bind >>
  rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  irule gas_outcome_ptr_conseq >>
      qexistsl_tac [`P`, `\res ee gt r. expr_exit res r`] >>
      rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> first_x_assum drule >>
          strip_tac >> gvs[] >>
          rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
          disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
          qexistsl_tac [`INR (ReturnException v)`, `ee`, `G2`, `tn2`, `Halt u`] >>
          simp[gas_explicit_def, raise_def, exit_result_def, stmt_exit_ptr_def])
      >- (rpt gen_tac >> simp[] >> strip_tac >>
          Cases_on `res` >> gvs[expr_exit_def] >>
          metis_tac[stmt_exit_ptr_def, expr_exit_INR_type]) >>
      first_assum ACCEPT_TAC
QED
