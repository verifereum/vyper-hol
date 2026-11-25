(* Compose the decorations on the very witnesses chosen by the initializer. *)
Theory entryCreateDefaultConsOutcome
Ancestors
  entryCreateOutcomeWitness gasOutcomeFull
  gasExemptCert gasStorage gasSummaryCompose fragGasOriginPtr fragGasOrigin
  vyperStorageFootprint vyperStorageTrace vyperInterpreter exprSimWordArgs
  vyperState fragGasMode gasSummary pair sum list

Theorem horizon_before_obs_run[local]:
  storage_trace_frame f /\
  f (src with gas_obs := xs) = (res,dst with gas_obs := ys) /\
  valid_horizon cx st0 H dst.storage_trace ==>
  valid_horizon cx st0 H src.storage_trace
Proof
  strip_tac >>
  `valid_horizon cx st0 H (dst with gas_obs := ys).storage_trace` by simp[] >>
  drule_all valid_horizon_frame >> simp[]
QED

Theorem witnessed_default_bind[local]:
  witnessed_operand_outcome F1 M1 (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (source : evaluation_state -> value evaluation_result) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) /\
  (!marks v mid G1 tn1 t.
     M1 s marks (OK t) /\
     (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H v mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
     witnessed_operand_outcome F2 M2 (DF,lo,explicit,ctx,fn,PG) tops cx st0
       (next v) (mid,t,G1,tn1) Q
       (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!left. F1 s left ==> focus s left) /\
  (!left r. M1 s left r /\ exit_result r ==> M s left r) /\
  (!left t right. M1 s left (OK t) /\ F2 t right ==> focus s (left ++ right)) /\
  (!left t right r. M1 s left (OK t) /\ M2 t right r ==> M s (left ++ right) r) ==>
  witnessed_operand_outcome focus M (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (bind source next) (es,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `witnessed_operand_outcome _ _ _ _ _ _ source _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [witnessed_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ source _ _ _`]
  >- (rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[]) >>
      conj_tac >- simp[] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (asm_rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac >- simp[] >> conj_tac
      >- (irule gas_exempt_cert_error_value >> simp[]) >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac))
  >~ [`r = OK t`]
  >- suspend "continue" >>
  rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR ex`,`ee`,`r`,`G'`,`tn'`] >>
  conj_tac >- simp[] >>
  conj_tac >- (irule gas_source_bind_exception >> fs[]) >>
  gvs[] >> rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]
QED

Resume witnessed_default_bind[continue]:
  gvs[] >>
  `witnessed_operand_outcome F2 M2 (DF,lo,explicit,ctx,fn,PG) tops cx st0
      (next v) (ee with gas_obs := [],t,G',tn') Q
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)` by
    (qpat_assum `!marks v mid G1 tn1 t. _ ==> witnessed_operand_outcome _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`marks`,`v`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,G',tn')` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
     metis_tac[horizon_before_obs_run]) >>
  `gas_marked_exec T (ctx,fn) source (es,s) marks (INL v) ee (OK t)` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections,gas_origin_path_erase]) >>
  `gas_path ctx fn s (LENGTH marks) (OK t)` by
    (fs[gas_marked_exec_def] >> metis_tac[gas_marked_path_exec]) >>
  qpat_x_assum `witnessed_operand_outcome _ _ _ _ _ _ (next v) _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [witnessed_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- suspend "bad_tail"
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- suspend "exempt_tail" >>
  suspend "full_tail"
QED

Resume witnessed_default_bind[bad_tail]:
  rewrite_tac[witnessed_operand_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >> conj_tac
  >- (irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
  conj_tac >- metis_tac[] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

Resume witnessed_default_bind[exempt_tail]:
  asm_rewrite_tac[witnessed_operand_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee'`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule gas_exempt_cert_bind_value >> qexistsl_tac [`ee`,`t`,`v`] >> fs[]) >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
  qexists_tac `H` >> conj_tac >- metis_tac[] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

Resume witnessed_default_bind[full_tail]:
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `!tail. next v _ = _`
       (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (next v)` by simp[] >>
     rpt strip_tac >> drule_all horizon_before_obs_run >> simp[]) >>
  drule gas_explicit_append_path >> disch_then (qspec_then `marks'` assume_tac) >>
  rewrite_tac[witnessed_operand_outcome_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee'`,`r`,`G''`,`tn''`] >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >>
      qexistsl_tac [`ee`,`v`] >> fs[]) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> res_tac >> simp[] >>
  irule gas_origin_ptr_path_append >> metis_tac[]
QED

Finalise witnessed_default_bind

Theorem witnessed_default_cons_map[local]:
  witnessed_operand_outcome focus M (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (eval_exprs cx xs) (es,s,G,tn)
    (\H res ee G' tn' t. ?vs. res = INL vs /\ Q H (v::vs) ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) ==>
  witnessed_operand_outcome focus M (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (bind (eval_exprs cx xs) (\vs. return (v::vs))) (es,s,G,tn)
    (\H res ee G' tn' t. ?vs. res = INL vs /\ Q H vs ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  `!src. bind (eval_exprs cx xs) (\vs. return (v::vs)) src =
     (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs src)),
      SND (eval_exprs cx xs src))` by
    (gen_tac >> Cases_on `eval_exprs cx xs src` >>
     rename1 `eval_exprs cx xs src = (rs,ee)` >>
     Cases_on `rs` >> simp[bind_def, return_def, sumTheory.SUM_MAP_def]) >>
  `ignore_bind (bind (eval_exprs cx xs) (\vs. return (v::vs))) (return ()) =
   ignore_bind (eval_exprs cx xs) (return ())` by
    simp[ignore_bind_def, bind_assoc, bind_return] >>
  simp[witnessed_operand_outcome_def,gas_bad_storage_at_def] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`sum$SUM_MAP (CONS v) I res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> res_tac >>
      fs[sumTheory.SUM_MAP_def] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem grouped_default_exprs_cons_witnessed:
  witnessed_operand_outcome F1 M1 (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) /\
  (!marks v mid G1 tn1 t.
     M1 s marks (OK t) /\
     (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H v mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
     witnessed_operand_outcome F2 M2 (DF,lo,explicit,ctx,fn,PG) tops cx st0
       (eval_exprs cx xs) (mid,t,G1,tn1)
       (\H res ee G' tn' u. ?vs. res = INL vs /\ Q H (v::vs) ee G' tn' u)
       (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  (!left. F1 s left ==> focus s left) /\
  (!left r. M1 s left r /\ exit_result r ==> M s left r) /\
  (!left t right. M1 s left (OK t) /\ F2 t right ==> focus s (left ++ right)) /\
  (!left t right r. M1 s left (OK t) /\ M2 t right r ==> M s (left ++ right) r) ==>
  witnessed_operand_outcome focus M (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (eval_exprs cx (e::xs)) (es,s,G,tn)
    (\H res ee G' tn' t. ?vs. res = INL vs /\ Q H vs ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >> rewrite_tac[eval_exprs_cons_action] >>
  irule witnessed_default_bind >>
  qpat_assum `witnessed_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`M2`,`F2`] >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_return] >>
  rpt conj_tac
  >- (rpt strip_tac >> ho_match_mp_tac witnessed_default_cons_map >>
      qpat_assum `!marks v mid G1 tn1 t. _ ==> witnessed_operand_outcome _ _ _ _ _ _ _ _ _ _`
        (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >> simp[])
  >> metis_tac[]
QED
