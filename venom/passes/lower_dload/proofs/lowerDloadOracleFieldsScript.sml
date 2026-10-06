(* TASK036: actual oracle-field coverage of the unchanged residual relations.
 * TOP-LEVEL: projections, exact coverage, paired-update constructors and
 * primitive-step transport. No change to LowerDload's scratch exceptions. *)
Theory lowerDloadOracleFields
Ancestors
  lowerDloadFrame lowerDloadDefs lowerDloadClassify
  venomState stateEquiv oracleExecProps

(* ===== Actual residual masks ===== *)

Theorem ld_frame_oracle[simp]:
  (ld_frame s).vs_outcomes = s.vs_outcomes /\
  (ld_frame s).vs_requests = s.vs_requests /\
  (ld_execution_frame s).vs_outcomes = s.vs_outcomes /\
  (ld_execution_frame s).vs_requests = s.vs_requests
Proof
  simp[ld_frame_def, ld_execution_frame_def]
QED

Theorem ld_frame_oracle_updates[simp]:
  ld_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    ld_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  ld_execution_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    ld_execution_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[ld_frame_def, ld_execution_frame_def]
QED

Theorem ld_frame_oracle_transport:
  (ld_frame s1 = ld_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (ld_execution_frame s1 = ld_execution_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac
  >- (strip_tac >> conj_tac >> irule ld_frame_projection >>
      simp_tac bool_ss [ld_frame_oracle] >> metis_tac[]) >>
  strip_tac >> conj_tac >> irule ld_execution_frame_projection >>
  simp_tac bool_ss [ld_frame_oracle] >> metis_tac[]
QED

(* ===== Formal audit: both named relations already include both lists ===== *)

Theorem ld_equiv_oracle:
  ld_equiv vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[ld_equiv_def] >> metis_tac[ld_frame_oracle_transport]
QED

Theorem ld_ok_oracle:
  ld_ok vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[ld_ok_def] >> metis_tac[ld_frame_oracle_transport]
QED

Theorem ld_relations_oracle_coverage:
  (ld_equiv vars s1 s2 <=>
    ld_equiv vars s1 s2 /\ s1.vs_outcomes = s2.vs_outcomes /\
    s1.vs_requests = s2.vs_requests) /\
  (ld_ok vars s1 s2 <=>
    ld_ok vars s1 s2 /\ s1.vs_outcomes = s2.vs_outcomes /\
    s1.vs_requests = s2.vs_requests)
Proof
  metis_tac[ld_equiv_oracle, ld_ok_oracle]
QED

(* Arbitrary list payloads, not default reconstruction. This iff exposes
   exactly the two new constructor obligations without dropping old clauses. *)
Theorem ld_relations_oracle_updates:
  (ld_equiv vars (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
                 (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
    ld_equiv vars (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
                  (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
    os1 = os2 /\ rqs1 = rqs2) /\
  (ld_ok vars (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
              (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
    ld_ok vars (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
               (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
    os1 = os2 /\ rqs1 = rqs2)
Proof
  simp[ld_equiv_def, ld_ok_def, ld_frame_def, ld_execution_frame_def,
       lookup_var_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem ld_relations_oracle_same_updates:
  (ld_equiv vars s1 s2 ==>
    ld_equiv vars (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
                  (s2 with <| vs_outcomes := os; vs_requests := rqs |>)) /\
  (ld_ok vars s1 s2 ==>
    ld_ok vars (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
               (s2 with <| vs_outcomes := os; vs_requests := rqs |>))
Proof
  simp[ld_equiv_def, ld_ok_def, lookup_var_def] >>
  metis_tac[ld_frame_oracle_updates]
QED

Theorem ld_relations_oracle_refl:
  ld_ok vars s s /\ ld_equiv vars s s
Proof
  simp[ld_ok_refl, ld_equiv_def]
QED

(* TASK035's concrete primitive preservation covers arbitrary opcodes and
   payloads, including concrete CALL; no new opcode/observability premise. *)
Theorem ld_ok_step_oracle:
  ld_ok vars s1 s2 /\
  step_inst_base inst1 s1 = OK t1 /\ step_inst_base inst2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[ld_ok_oracle, step_inst_base_oracle]
QED

(* Error has no state projection. All four state-bearing constructors use
   the very same field relation; IntRet values and abort codes stay compared. *)
Theorem ld_lift_result_oracle:
  lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[ld_ok_oracle, ld_equiv_oracle]
QED
