(* Arbitrary oracle payload constructors; no empty-default assumptions. *)
Theory coreOracleUpdates
Ancestors
  coreOracleCoverage oracleStateProps stateEquiv stateFrame venomState
  execEquivParamDefs execEquivParamBase

(* Equality congruence plus mask/update commutation, shared by both families. *)
Theorem oracle_mask_same_updates:
  (!s os rqs. mask (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    mask s with <| vs_outcomes := os; vs_requests := rqs |>) /\
  mask s1 = mask s2 ==>
  mask (s1 with <| vs_outcomes := os; vs_requests := rqs |>) =
  mask (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  rpt strip_tac >> simp[]
QED

Theorem core_oracle_same_updates:
  (execution_equiv vars s1 s2 ==>
    execution_equiv vars (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
      (s2 with <| vs_outcomes := os; vs_requests := rqs |>)) /\
  (state_equiv vars s1 s2 ==>
    state_equiv vars (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
      (s2 with <| vs_outcomes := os; vs_requests := rqs |>))
Proof
  simp_tac bool_ss [execution_equiv_def, state_equiv_frame,
    lookup_var_def, oracle_frame_updates, Excl "core_complete_mask_equality"] >>
  rpt strip_tac >> simp[]
QED

Theorem core_oracle_updates:
  (execution_equiv vars
      (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
      (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
    execution_equiv vars
      (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
      (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
    os1 = os2 /\ rqs1 = rqs2) /\
  (state_equiv vars
      (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
      (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
    state_equiv vars
      (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
      (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
    os1 = os2 /\ rqs1 = rqs2)
Proof
  conj_tac >> eq_tac >> strip_tac >> gvs[] >>
  FIRST [drule execution_equiv_oracle, drule state_equiv_oracle] >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem vsr_oracle_pair_updates[simp]:
  vsr_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    vsr_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  vsr_term_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    vsr_term_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[vsr_frame_def, vsr_term_frame_def]
QED

Theorem valid_state_rel_oracle_same_updates:
  valid_state_rel R_ok R_term ==>
  (!s1 s2 os rqs. R_ok s1 s2 ==>
    R_ok (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
      (s2 with <| vs_outcomes := os; vs_requests := rqs |>)) /\
  (!s1 s2 os rqs. R_term s1 s2 ==>
    R_term (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
      (s2 with <| vs_outcomes := os; vs_requests := rqs |>))
Proof
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (drule_all vsr_R_ok_frame >> strip_tac >>
      irule vsr_reconstruct_R_ok >>
      simp[Excl "vsr_complete_mask_equality"] >>
      metis_tac[]) >>
  drule_all vsr_R_term_frame >> strip_tac >>
  irule vsr_reconstruct_R_term >>
  simp[Excl "vsr_complete_mask_equality"] >> metis_tac[]
QED

(* Exact independent-payload characterization uses only retained projections;
 * it applies to arbitrary running/terminal relations satisfying the contract. *)
Theorem oracle_relation_updates:
  (!s1 s2. R s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) ==>
  (R (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
     (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
   R (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
     (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
   os1 = os2 /\ rqs1 = rqs2)
Proof
  strip_tac >> eq_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!s1 s2. _` drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem valid_state_rel_oracle_updates:
  valid_state_rel R_ok R_term ==>
  (R_ok (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
        (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
   R_ok (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
        (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
   os1 = os2 /\ rqs1 = rqs2) /\
  (R_term (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
          (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
   R_term (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
          (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
   os1 = os2 /\ rqs1 = rqs2)
Proof
  strip_tac >> drule valid_state_rel_oracle >> strip_tac >>
  conj_tac >> irule oracle_relation_updates >> simp[]
QED
