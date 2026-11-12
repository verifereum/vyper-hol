(* Gas-aware value sequencing shared by slice operand consumers. *)
Theory exprSimSliceCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert vyperState vyperValue
  fragGasSeq fragGasMode stmtSimDeclCompose list exprSimDefs gasContext

Theorem slice_gas_outcome_bind_value:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func) a (es,s) marks (INL v) mid (OK t) /\
    P v (mid with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func) (k v) (mid with gas_obs := [],t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> first_x_assum drule_all >>
      rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
      >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal])
      >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal]) >>
      qexists_tac `marks ++ marks'` >> disj2_tac >>
      rewrite_tac[ignore_bind_def, bind_assoc] >>
      qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
      irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> fs[ignore_bind_def])
  >- (gvs[] >> qexists_tac `marks` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_exception]) >>
  qexists_tac `marks` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem slice_gas_outcome_conseq:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!res ee t. Q res ee t ==> Q' res ee t) /\
  (!res ee r. R res ee r ==> R' res ee r) ==>
  gas_outcome memory tops (ctx,func) source (es,s) Q' R'
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
  gas_outcome F tops (ctx,func) source
    (es,t with vs_inst_idx := s.vs_inst_idx + LENGTH code) Q R ==>
  gas_outcome F tops (ctx,func) source (es,s) Q R
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
