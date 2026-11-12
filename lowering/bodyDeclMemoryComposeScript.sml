(* Counted memory composition of a declaration: the local's ALLOCA, the
   right-hand side's source action, then the store that binds the local.
   The memory-mode twins of stmtSimDeclCompose's annassign_rhs_outcome and
   annassign_outcome_entry_prefix. *)
Theory bodyDeclMemoryCompose
Ancestors
  stmtSimDeclCompose stmtSimDeclGas stmtSimDeclSource gasSummary
  gasSummaryCompose gasOutcome gasStorage gasExemptCert fragGasMode fragGasPathMem
  vyperStorageTrace vyperStorageFootprint
  stmtSimDefs stmtSimProps exprSimDefs vyperInterpreter vyperState list
Libs monadsyntax

Theorem gas_marked_exec_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_marked_exec T (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec T (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `gas_marked_path T ctx func s0 0 (OK s1)` by simp[gas_marked_path_def] >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  fs[gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem gas_exempt_cert_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_exempt_cert T tops (ctx,func) source (es,s1) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert T tops (ctx,func) source (es,s0) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, return_def, gas_marked_path_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem gas_outcome_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_outcome T tops (ctx,func) cx st0 source (es,s1) Q R ==>
  gas_outcome T tops (ctx,func) cx st0 source (es,s0) Q R
Proof
  strip_tac >>
  `gas_marked_path T ctx func s0 0 (OK s1)` by simp[gas_marked_path_def] >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_zero_prefix_mem]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_zero_prefix_mem >> qexists_tac `s1` >> simp[]
QED

(* The declaration's source action from the state after the local's
   ALLOCA (salloc): the right-hand side's outcome, and the binding of the
   local after a value, which the caller supplies with the post P.  A
   right-hand side whose storage trace has no valid horizon makes the whole
   declaration's trace invalid, since the binding adds no observation. *)
Theorem annassign_rhs_outcome_mem:
  !ctx func cx st0 RetQ id typ tyv e es s0 salloc tops Q P.
    gas_path_mem ctx func s0 0 (OK salloc) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome T tops (ctx,func) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,salloc) Q
      (\H res ee r. expr_exit res r) /\
    (!H res ee t. Q H res ee t ==> ?v. res = INL v) /\
    (!marks v ee t.
      gas_marked_exec T (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,salloc)
        marks (INL v) ee (OK t) /\
      (?H. valid_horizon cx st0 H ee.storage_trace) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           Q H (INL v) (ee with gas_obs := []) t) ==>
      ?ff u. gas_marked_exec T (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        (!H. valid_horizon cx st0 H ff.storage_trace ==>
             P H (INL ()) (ff with gas_obs := []) u)) ==>
    gas_outcome T tops (ctx,func) cx st0
      (eval_stmt cx (AnnAssign id typ e)) (es,s0) P
      (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `salloc` >> simp[] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_new_variable])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choosel_then [`res`, `es_end`, `r`]
        (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
      qexists_tac `marks` >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_new_variable] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disj2_tac >> disj1_tac >>
      qpat_x_assum `_ \/ _` strip_assume_tac
      >- (gvs[] >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          qpat_x_assum `!marks v ee t. _` (drule_then mp_tac) >>
          (impl_tac
           >- (conj_tac
               >- (qexists_tac `storage_trace_horizon es_end.storage_trace` >>
                   simp[]) >>
               simp[])) >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end with gas_obs := []`, `t`, `v`] >>
          simp[] >> irule gas_marked_exec_end_gas_obs >> simp[]) >>
      gvs[] >>
      `expr_exit res r` by metis_tac[] >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> rpt strip_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  simp[ignore_bind_def]
QED
