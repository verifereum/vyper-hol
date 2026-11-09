(* Counted local updates after a right-hand-side memory outcome. *)
Theory widenedLocalOutcomeMem
Ancestors
  bodyDeclMemoryCompose stmtReasonVvMemory stmtSimDeclGas gasSummary
  gasOutcome gasSummaryCompose fragGasMode stmtSimDefs vyperInterpreter
  vyperState stmtSimDeclSource exprSimDefs exprSimProps stmtSimProps
  stmtSimAssignCompose stmtSimAssignSource gasExemptCert stmtSimDeclCompose
Libs monadsyntax

Theorem annassign_rhs_counted_outcome_mem:
  !ctx func cx RetQ id typ tyv e es s0 salloc tops Q P.
    gas_path_mem ctx func s0 0 (OK salloc) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome T tops (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,salloc) Q
      (\res ee r. expr_exit res r) /\
    (!res ee t. Q res ee t ==> ?v. res = INL v) /\
    (!marks v ee t.
      gas_marked_exec T (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,salloc)
        marks (INL v) ee (OK t) /\
      Q (INL v) (ee with gas_obs := []) t ==>
      ?marks' ff u. gas_marked_exec T (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) marks' (INL ()) ff (OK u) /\
        P (INL ()) (ff with gas_obs := []) u) ==>
    gas_outcome T tops (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,s0) P
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_zero_prefix_mem >> qexists `salloc` >> simp[] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?v. res = INL v` by metis_tac[] >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      simp[gas_outcome_def] >>
      qexists `marks'` >> disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists `y` >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Theorem assign_local_rhs_counted_outcome_mem:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) Q
    (\res ee r. expr_exit res r) /\
  (!res ee t. Q res ee t ==> ?v. res = INL v) /\
  (!marks v ee t.
    gas_marked_exec T (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      marks (INL v) ee (OK t) /\ Q (INL v) (ee with gas_obs := []) t ==>
    ?right ff u. gas_marked_exec T (ctx,func)
      (write_place cx (MemoryPlace id []) v)
      (ee with gas_obs := [],t) right (INL ()) ff (OK u) /\
      P (INL ()) (ff with gas_obs := []) u) ==>
  gas_outcome T tops (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (es,s0) P
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          first_x_assum drule_all >> strip_tac >>
          qexists `marks ++ right` >> disj1_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_normal >>
          qexistsl_tac [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
          irule gas_marked_exec_end_gas_obs >> simp[]) >>
      qexists `marks` >> disj1_tac >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule assign_local_marked_exec >>
          (conj_tac >- (qexists `lctx` >> simp[])) >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_local_exempt >> simp[gas_exempt_cert_unforce_result]
QED
