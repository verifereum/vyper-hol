(* Gas-aware value sequencing shared by slice operand consumers. *)
Theory exprSimSliceCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasStorage
  vyperStorageTrace vyperStorageFootprint vyperState vyperValue
  fragGasSeq fragGasMode stmtSimDeclCompose list exprSimDefs gasContext

Theorem slice_gas_outcome_bind_value:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> value evaluation_result) (es,s)
    (\H res ee t. ?v. res = INL v /\ P H v ee t)
    (\H res ee r. ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!v. storage_trace_frame (k v)) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func) a (es,s) marks (INL v) mid (OK t) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H v (mid with gas_obs := []) t) ==>
    gas_outcome memory tops (ctx,func) cx st0 (k v)
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           drule_all gas_bad_storage_at_counted_prefix >> simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "normal"
      >> suspend "exit") >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_error_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Resume slice_gas_outcome_bind_value[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?v. res = INL v` by
    (first_assum (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!marks v mid t. _`
    (qspecl_then [`marks`, `v`, `es_end`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ (k _) _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> irule gas_bad_storage_at_bind_right >> simp[] >>
      metis_tac[])
  >- (qpat_x_assum `gas_summary_at _ _ _ (k _) _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
      (conj_tac
       >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
           gvs[])) >>
      fs[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
  disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_bind_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Resume slice_gas_outcome_bind_value[exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?ex. res = INR ex` by
    (first_assum (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> metis_tac[]) >>
  gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED

Finalise slice_gas_outcome_bind_value

Theorem slice_gas_outcome_conseq:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R /\
  (!H res ee t. Q H res ee t ==> Q' H res ee t) /\
  (!H res ee r. R H res ee r ==> R' H res ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q' R'
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

(* A capture fragment consumes no source action and no GAS reading. *)
Theorem slice_capture_outcome_prefix:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS) code /\
  run_inst_seq code s = OK t /\
  gas_outcome F tops (ctx,func) cx st0 source
    (es,t with vs_inst_idx := s.vs_inst_idx + LENGTH code) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 source (es,s) Q R
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code`
    by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  irule gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  simp[gas_marked_path_def] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[]
QED

Theorem slice_gas_admissible_bind_head:
  gas_admissible (bind a k) Q es /\
  (!v. P (INL v)) /\ (!ex. Q (INR ex) ==> P (INR ex)) ==>
  gas_admissible a P es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >> simp[] >>
  first_x_assum irule >>
  qpat_x_assum `!gs res ee. _ ==> Q res` irule >>
  qexistsl_tac [`ee`, `gs`] >> simp[bind_def]
QED

Theorem slice_gas_admissible_expr_head:
  gas_admissible
    (bind (a : evaluation_state -> value evaluation_result) k)
    expr_vv_res_ok es ==>
  gas_admissible a expr_res_ok es
Proof
  strip_tac >> drule slice_gas_admissible_bind_head >>
  disch_then (qspec_then `expr_res_ok` mp_tac) >>
  simp[expr_res_ok_def, expr_vv_res_ok_def]
QED

Theorem slice_gas_admissible_value_head:
  gas_admissible
    (bind (a : evaluation_state -> value evaluation_result) k)
    expr_res_ok es ==>
  gas_admissible a expr_res_ok es
Proof
  strip_tac >> drule slice_gas_admissible_bind_head >>
  disch_then (qspec_then `expr_res_ok` mp_tac) >> simp[expr_res_ok_def]
QED
