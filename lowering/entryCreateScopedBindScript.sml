(* Sequencing uses the two chosen witnesses, not fresh outcomes at each
   horizon. The geometric premises describe only how scopes embed. *)
Theory entryCreateScopedBind
Ancestors
  entryCreateCompletedCut entryCreateFocusSpec gasSummaryCompose
  fragGasOriginPtr fragGasOrigin fragGasPath fragGasMode fragExec
  gasStorage gasExemptCert gasSummary vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState list

Theorem scoped_horizon_at_start[local]:
  storage_trace_frame f /\
  (!tail. f (es with gas_obs := xs ++ tail) = (res, ee with gas_obs := tail)) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  qpat_assum `!tail. f _ = _` (qspec_then `[]` mp_tac) >>
  strip_tac >>
  `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
  drule_all valid_horizon_frame >> simp[]
QED

(* Prepend a successful left witness to any of the three right branches. *)
Theorem scoped_operand_bind_right[local]:
  (!tail. source (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (s,G,tn) left (OK t,G1,tn1)) /\
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 m b
    (next v) (mid with gas_obs := [],t,G1,tn1) Q R /\
  storage_trace_frame (next v) /\
  (!right err ee leaf finish.
     gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx,func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
  (!right. create_operand_focus_scope m b explicit ctx func t right ==>
     create_operand_focus_scope a b explicit ctx func s (left ++ right)) /\
  (!right r. create_operand_full_scope m b explicit ctx func t right r ==>
     create_operand_full_scope a b explicit ctx func s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t)` by
    (fs[storage_trace_domain_def,gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections,gas_origin_path_erase]) >>
  `gas_path ctx func s (LENGTH left) (OK t)` by
    metis_tac[gas_marked_exec_def,gas_marked_path_exec] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ m b _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `left ++ marks` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `left ++ marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
      `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
      qexists_tac `H` >> conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     valid_horizon cx st0 H mid.storage_trace` by
     (rpt strip_tac >> drule_all scoped_horizon_at_start >> simp[]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `left ++ marks` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (drule gas_explicit_append_path >> disch_then (qspec_then `marks` SUBST1_TAC) >>
      irule gas_source_bind_normal >> qexistsl_tac [`mid`,`v`] >> fs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> res_tac >> simp[] >>
  irule gas_origin_ptr_path_append >> metis_tac[]
QED

Theorem scoped_operand_bind_all_mixed:
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a m
    source (es,s,G,tn) Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     create_operand_at m t /\
     create_operand_full_scope a m explicit ctx func s marks (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                                   (s,G,tn) marks (OK t,G1,tn1)) ==>
     ?v. res = INL v /\ scoped_operand_outcome (DF,lo,explicit,ctx,func,PG)
             tops cx st0 m b (next v) (mid,t,G1,tn1) Q R) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf finish.
     gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) marks (err,ee) (leaf,finish)) /\
  (!left v mid t right err ee leaf finish.
     gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx,func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
  (!marks. create_operand_focus_scope a m explicit ctx func s marks ==>
     create_operand_focus_scope a b explicit ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m explicit ctx func s marks r ==>
     create_operand_full_scope a b explicit ctx func s marks r) /\
  (!left t right.
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     create_operand_focus_scope m b explicit ctx func t right ==>
     create_operand_focus_scope a b explicit ctx func s (left ++ right)) /\
  (!left t right r.
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     create_operand_full_scope m b explicit ctx func t right r ==>
     create_operand_full_scope a b explicit ctx func s (left ++ right) r) ==>
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
  qpat_x_assum `!marks res mid G1 tn1 t. _ ==> _`
    (qspecl_then [`marks`,`res`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  irule scoped_operand_bind_right >>
  first_assum (irule_at Any) >> simp[] >>
  rpt conj_tac >> metis_tac[scoped_horizon_at_start]
QED

Theorem scoped_operand_bind_all:
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a m
    source (es,s,G,tn) Q1 (\H res ee gt r. (?exc. res = INR exc) /\ R H res ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
         (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     create_operand_at m t /\
     create_operand_full_scope a m explicit ctx func s marks (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                                   (s,G,tn) marks (OK t,G1,tn1)) ==>
     ?v. res = INL v /\ scoped_operand_outcome (DF,lo,explicit,ctx,func,PG)
             tops cx st0 m b (next v) (mid,t,G1,tn1) Q R) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf finish.
     gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) marks (err,ee) (leaf,finish)) /\
  (!left v mid t right err ee leaf finish.
     gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx,func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
       (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
  (!marks. create_operand_focus_scope a m explicit ctx func s marks ==>
     create_operand_focus_scope a b explicit ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m explicit ctx func s marks r ==>
     create_operand_full_scope a b explicit ctx func s marks r) /\
  (!left t right.
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     create_operand_focus_scope m b explicit ctx func t right ==>
     create_operand_focus_scope a b explicit ctx func s (left ++ right)) /\
  (!left t right r.
     create_operand_full_scope a m explicit ctx func s left (OK t) /\
     create_operand_full_scope m b explicit ctx func t right r ==>
     create_operand_full_scope a b explicit ctx func s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  `(\H res ee gt r. (?exc. res = INR exc) /\ R H res ee gt r) =
   (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum (fn eq =>
    qpat_x_assum `scoped_operand_outcome _ _ _ _ a m _ _ _ _`
      (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  irule scoped_operand_bind_all_mixed >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Q1`,`m`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
