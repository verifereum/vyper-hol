(* A terminal continuation can run after the child or focus at its exit. *)
Theory entryCreateTerminalBind
Ancestors
  entryCreateCompletedCut entryCreateFocusSpec entryCreatePendingScope
  gasSummaryCompose fragGasOriginPtr fragGasOrigin fragGasPath fragGasMode
  fragExec gasStorage gasExemptCert gasSummary vyperStorageTrace
  vyperStorageFootprint vyperInterpreter vyperState list

Theorem scoped_terminal_bind_at_child:
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a m
    source (es,s,G,tn) Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!left res mid G1 tn1 t.
     (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
         (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     create_operand_at m t /\
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                                   (s,G,tn) left (OK t,G1,tn1)) ==>
     ?v. res = INL v /\
       ((?exc fin r G2 tn2.
          (!tail. next v (mid with gas_obs := tail) = (INR exc, fin with gas_obs := tail)) /\
          storage_trace_domain cx st0 fin.storage_trace /\
          exit_result r /\ create_operand_full_scope m b explicit ctx func t [] r /\
          (!H. valid_horizon cx st0 H fin.storage_trace ==>
             valid_horizon cx st0 H mid.storage_trace /\
             gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
               (t,G1,tn1) [] (r,G2,tn2) /\
             R H (INR exc) (fin with gas_obs := []) (G2,tn2) r)) \/
        (?err fin H. valid_horizon cx st0 H mid.storage_trace /\
          gas_exempt_cert T tops (ctx,func)
            (ignore_bind (bind source next) (return ()))
            (es,s) left (err,fin) (func,t)))) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf finish.
     gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) marks (err,ee) (leaf,finish)) /\
  (!marks. create_operand_focus_scope a m explicit ctx func s marks ==>
     create_operand_focus_scope a b explicit ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m explicit ctx func s marks r ==>
     create_operand_full_scope a b explicit ctx func s marks r) /\
  (!left t. create_expr_prefix a m explicit ctx func s left t ==>
     create_expr_prefix a b explicit ctx func s left t) /\
  (!left t r.
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     create_operand_full_scope m b explicit ctx func t [] r ==>
     create_operand_full_scope a b explicit ctx func s left r) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ a m _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [scoped_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ source _ _ _`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac >- (irule gas_bad_storage_at_bind_left >> simp[]) >>
      metis_tac[])
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  Cases_on `exit_result r`
  >- (`!H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (r,G',tn') /\
           (?exc. res = INR exc /\ R H (INR exc) (ee with gas_obs := []) (G',tn') r)` by
         (rpt strip_tac >> res_tac >> fs[exit_result_def]) >>
      `?exc. res = INR exc` by metis_tac[storage_trace_domain_def] >> gvs[] >>
      rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >> metis_tac[]) >>
  `?t. r = OK t` by metis_tac[storage_trace_domain_def] >> gvs[] >>
  `create_operand_at m t` by fs[create_operand_full_scope_def,create_operand_at_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     Q1 H res (ee with gas_obs := []) G' tn' t /\
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn')` by
    (rpt strip_tac >> res_tac >> fs[]) >>
  qpat_x_assum `!left res mid G1 tn1 t. _ ==> _`
    (qspecl_then [`marks`,`res`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
  >~ [`exit_result r`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`INR exc`,`fin`,`r`,`G2`,`tn2`] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- simp[bind_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> simp[] >>
      metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`,`fin`,`func`,`PG`,`G'`,`tn'`,`t`] >>
  conj_tac >-
    (irule create_operand_focus_scope_caller >> qexists_tac `t` >>
     qpat_assum `!left t. create_expr_prefix a m _ _ _ _ left t ==> _` irule >>
     fs[create_operand_full_scope_def]) >>
  simp[] >> qexists_tac `H` >> conj_tac
  >- (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
      `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
      drule_all valid_horizon_frame >> simp[]) >>
  irule (cj 1 gas_origin_ptr_focus_rules) >> metis_tac[]
QED
