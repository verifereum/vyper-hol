(* TASK038: oracle projection for ALL four state-bearing result constructors.
 * Abort codes and IntRet values keep the original lift_result comparisons;
 * Error remains state-free. No replacement result relation or simulator. *)
Theory remainingOracleLift
Ancestors
  remainingOracleCoverage passSimulationDefs passSimulationProps
  copyFwdEquiv invokeCopyFwdCommonDefs deadStoreElimDefs deadStoreElimProofs
  mem2varDefs mem2varBlockSimHelpers mmCorrectnessProofs
  venomExecSemantics venomState stateEquiv oracleStateProps

Theorem oracle_relation_lift_result:
  (!s1 s2. R_ok s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (!s1 s2. R_halt s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (!s1 s2. R_abort s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  lift_result R_ok R_halt R_abort r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[]
QED

Theorem copy_fwd_rel_lift_result_oracle:
  lift_result (copy_fwd_rel dst src sz) (copy_fwd_rel dst src sz)
    (copy_fwd_rel dst src sz) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[copy_fwd_rel_oracle]
QED

Theorem icf_equiv_lift_result_oracle:
  lift_result icf_equiv icf_equiv icf_equiv r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[icf_equiv_oracle]
QED

Theorem dse_equiv_lift_result_oracle:
  lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[dse_equiv_oracle]
QED

Theorem dse_all_equiv_lift_result_oracle:
  lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[dse_all_equiv_oracle]
QED

Theorem m2v_equiv_lift_result_oracle:
  lift_result (m2v_equiv vars) (m2v_equiv vars) (m2v_equiv vars) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[m2v_equiv_oracle]
QED

Theorem m2v_inv_noix_lift_result_oracle:
  lift_result (m2v_inv_noix fn) (m2v_inv_noix fn) (m2v_inv_noix fn) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[m2v_inv_noix_oracle]
QED

Theorem memzero_inv_lift_result_oracle:
  lift_result (memzero_inv fresh) (memzero_inv fresh) (memzero_inv fresh) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[memzero_inv_oracle]
QED

Theorem R_dse_ok_lift_result_oracle:
  lift_result (R_dse_ok space) (dse_equiv space) (dse_equiv space) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[R_dse_ok_oracle, dse_equiv_oracle]
QED

(* Accept any refinement P of the original OK invariant. This covers the
   non32/undefined-variable/allocation tail used by actual block simulation. *)
Theorem m2v_inv_lift_result_oracle:
  lift_result (\s1 s2. m2v_inv fn s1 s2 /\ P s1 s2)
    (m2v_equiv (m2v_fresh_vars fn)) (m2v_equiv (m2v_fresh_vars fn)) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[m2v_inv_oracle, m2v_equiv_oracle]
QED

(* Actual memzero block/function boundary uses the existing core relations. *)
Theorem remaining_state_equiv_oracle:
  (state_equiv vars s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (execution_equiv vars s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac
  >- (simp[state_equiv_def, execution_equiv_def] >> rpt strip_tac >>
      irule oracle_state_frame_transport >> fs[]) >>
  simp[execution_equiv_def] >> rpt strip_tac >>
  irule oracle_execution_frame_transport >> fs[]
QED

Theorem remaining_state_lift_result_oracle:
  lift_result (state_equiv vars) (execution_equiv vars)
    (execution_equiv vars) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[remaining_state_equiv_oracle]
QED
