(* TASK036: actual oracle-field coverage of unchanged SSA residual relations.
 * TOP-LEVEL: projections, exact coverage, paired-update constructors and
 * primitive/result transport. Sigma remains directional; indices stay erased. *)
Theory ssaOracleFields
Ancestors
  ssaFrame ssaSimDefs venomState stateEquiv oracleExecProps

(* ===== Actual residual masks ===== *)

Theorem ssa_frame_oracle[simp]:
  (ssa_frame s).vs_outcomes = s.vs_outcomes /\
  (ssa_frame s).vs_requests = s.vs_requests /\
  (ssa_execution_frame s).vs_outcomes = s.vs_outcomes /\
  (ssa_execution_frame s).vs_requests = s.vs_requests
Proof
  simp[ssa_frame_def, ssa_execution_frame_def]
QED

Theorem ssa_frame_oracle_updates[simp]:
  ssa_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    ssa_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  ssa_execution_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    ssa_execution_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[ssa_frame_def, ssa_execution_frame_def]
QED

Theorem ssa_frame_oracle_transport:
  (ssa_frame s1 = ssa_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (ssa_execution_frame s1 = ssa_execution_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac
  >- (strip_tac >> conj_tac >> irule ssa_frame_projection >>
      simp_tac bool_ss [ssa_frame_oracle] >> metis_tac[]) >>
  strip_tac >> conj_tac >> irule ssa_execution_frame_projection >>
  simp_tac bool_ss [ssa_frame_oracle] >> metis_tac[]
QED

(* ===== Formal audit: the running relation already includes both lists ===== *)

Theorem ssa_sim_oracle:
  ssa_sim sigma s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[ssa_sim_def] >> metis_tac[ssa_frame_oracle_transport]
QED

Theorem ssa_sim_oracle_coverage:
  ssa_sim sigma s1 s2 <=>
  ssa_sim sigma s1 s2 /\ s1.vs_outcomes = s2.vs_outcomes /\
  s1.vs_requests = s2.vs_requests
Proof
  metis_tac[ssa_sim_oracle]
QED

(* Exact constructor obligations for arbitrary payloads, with no defaults. *)
Theorem ssa_sim_oracle_updates:
  ssa_sim sigma (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
                (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  ssa_sim sigma (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
                (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  simp[ssa_sim_def, ssa_frame_def, lookup_var_def,
       venom_state_component_equality] >> metis_tac[]
QED

Theorem ssa_sim_oracle_same_updates:
  ssa_sim sigma s1 s2 ==>
  ssa_sim sigma (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
                (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[ssa_sim_def, lookup_var_def] >> metis_tac[ssa_frame_oracle_updates]
QED

Theorem ssa_sim_oracle_refl:
  ssa_sim I s s /\
  ssa_sim I (s with <| vs_outcomes := os; vs_requests := rqs |>)
            (s with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[ssa_sim_identity]
QED

(* TASK035 preservation: no restriction on the two primitive opcodes. *)
Theorem ssa_sim_step_oracle:
  ssa_sim sigma s1 s2 /\
  step_inst_base inst1 s1 = OK t1 /\ step_inst_base inst2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[ssa_sim_oracle, step_inst_base_oracle]
QED

(* All state-bearing results, including Abort and IntRet, retain both lists.
   Error remains state-free; no new result/semantic relation is defined. *)
Theorem ssa_result_equiv_oracle:
  ssa_result_equiv r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[ssa_result_equiv_def, lift_result_def, execution_equiv_UNIV] >>
  metis_tac[ssa_sim_oracle, ssa_frame_oracle_transport]
QED

Theorem result_equiv_oracle:
  result_equiv vars r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[result_equiv_def, lift_result_def, state_equiv_def,
       execution_equiv_def] >>
  metis_tac[oracleStatePropsTheory.oracle_state_frame_transport,
            oracleStatePropsTheory.oracle_execution_frame_transport]
QED
