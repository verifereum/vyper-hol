(* Function handling preserves counted body exits and exempt certificates. *)
Theory bodyIntCallPackageHandler
Ancestors
  bodyIntCallPackagePrefix bodyIntCallHandler bodyIntCallJointContract
  gasOutcome gasSummary gasExemptCert exprSimDefs vyperInterpreter vyperState
Libs
  monadsyntax

Theorem gas_outcome_function_body:
  gas_outcome F tops (ctx,func) a (es,s0) Q (intcall_stmt_exit fp) /\
  (!marks res mid u.
    gas_marked_exec F (ctx,func) a (es,s0) marks res mid (OK u) /\
    Q res (mid with gas_obs := []) u ==>
    res = INL () /\ ?r. gas_path ctx func u 0 r /\ exit_result r /\
      R (INL NoneV) (mid with gas_obs := []) r) /\
  (!v ee r. intcall_stmt_exit fp (INR (ReturnException v)) ee r ==>
    R (INL v) ee r) /\
  (!res ee r. expr_exit res r ==> R res ee r) ==>
  gas_outcome F tops (ctx,func)
    (try (ignore_bind a (return NoneV)) handle_function) (es,s0)
    (\res ee u. F) R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac
      >- suspend "normal"
      >> suspend "terminal") >>
  disj2_tac >> qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  irule function_body_exempt_handler >> simp[]
QED

Resume gas_outcome_function_body[normal]:
  gvs[] >> first_x_assum drule_all >> strip_tac >> gvs[] >>
  qexistsl [`INL NoneV`, `es_end`, `r`] >> simp[] >>
  irule function_body_marked_handler >> qexistsl [`es_end`, `INL ()`] >> simp[return_def] >>
  irule gas_marked_exec_zero_suffix >> qexists `t` >> simp[]
QED

Resume gas_outcome_function_body[terminal]:
  qpat_assum `intcall_stmt_exit _ _ _ _` mp_tac >>
  rewrite_tac[intcall_stmt_exit_def] >> strip_tac
  >- (rename1 `expr_exit res r` >>
      Cases_on `res` >> Cases_on `r` >> gvs[expr_exit_def] >>
      rename1 `gas_marked_exec _ _ _ _ _ (INR ex) mid (Abort why u)` >>
      qexistsl [`INR ex`, `mid`, `Abort why u`] >> simp[] >>
      conj_tac
      >- (irule function_body_marked_handler >>
          qexistsl [`mid`, `INR ex`] >>
          Cases_on `ex` >> gvs[expr_exit_def, handle_function_def, raise_def] >>
          rename1 `Error err` >> Cases_on `err` >>
          gvs[expr_exit_def, handle_function_def, raise_def]) >>
      qspecl_then [`\u:unit. NoneV`, `INR ex`] mp_tac expr_exit_success_map >>
      simp[FUN_EQ_THM] >> metis_tac[])
  >> suspend "return"
QED

Resume gas_outcome_function_body[return]:
  gvs[] >> qexistsl [`INL v`, `es_end`, `IntRet ir u`] >> simp[] >>
  irule function_body_marked_handler >>
  qexistsl [`es_end`, `INR (ReturnException v)`] >>
  simp[handle_function_def, return_def]
QED
Finalise gas_outcome_function_body
