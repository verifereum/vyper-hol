(* Expose the actual marked prefix to its continuation.  This deliberately
   does not replace it with another outcome having independently chosen marks. *)
Theory bodyPtrMakeArrayConsBind
Ancestors
  gasSummaryComposePtrAll gasSummaryComposePtr fragGasPathPtr gasExemptCert gasSummary vyperState

Theorem literal_marked_exec_end_gas_obs:
  gas_marked_exec_ptr D (ctx,func) PG source start marks res
    (ee with gas_obs := gs) G tn r <=>
  gas_marked_exec_ptr D (ctx,func) PG source start marks res ee G tn r
Proof
  PairCases_on `start` >> simp[gas_marked_exec_ptr_def]
QED

Theorem literal_result_bind_outcome_ptr:
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (a : evaluation_state -> eval_result evaluation_result) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ ChildPost H v ee G tn t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks v ee G tn t.
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_marked_exec_ptr (D H) (ctx,func) PG a (es,s0,G0,tn0)
        marks (INL v) ee G tn (OK t) /\ ChildPost H v ee G tn t) /\
    ee.gas_obs = [] ==>
    gas_outcome_ptr D tops (ctx,func) PG cx st0
      (k v : evaluation_state -> 'b evaluation_result) (ee,t,G,tn) Q R) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind a k) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`source` |-> `a`, `next` |-> `k`,
     `P` |-> `\H res ee G tn t. ?v. res = INL v /\ ChildPost H v ee G tn t`,
     `E` |-> `\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r`]
    (INST_TYPE [alpha |-> ``:eval_result``] gas_outcome_ptr_bind_all)) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> gvs[])
      >- simp[]
      >- first_assum ACCEPT_TAC
      >- (rpt gen_tac >> strip_tac >>
          qpat_x_assum `!marks v ee G tn t. _`
            (qspecl_then [`left`, `v`, `mid with gas_obs := []`,
                          `G`, `tn`, `t`] mp_tac) >>
          impl_tac
          >- (simp[] >> conj_tac >- metis_tac[] >>
              rpt strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[gas_marked_exec_ptr_def, gas_marked_exec_def,
                  fragGasModeTheory.gas_marked_path_def]) >>
          simp[])
      >- (rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_error_result >> simp[GSYM ignore_bind_def]) >>
      rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]) >>
  simp[]
QED
