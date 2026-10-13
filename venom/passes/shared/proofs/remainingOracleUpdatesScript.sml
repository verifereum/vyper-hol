(* TASK038: arbitrary paired constructors, preserving the SAME relations.
 * TOP-LEVEL: mask commutation; synchronized constructors and exact iff.
 * No default lists or weakened memory/partial-variable/FMP contracts. *)
Theory remainingOracleUpdates
Ancestors
  remainingOracleCoverage passResidualFrame copyFwdEquiv invokeCopyFwdCommonDefs
  deadStoreElimFrame deadStoreElimDefs deadStoreElimProofs
  mem2varFrame mem2varDefs mem2varBlockSimHelpers
  memzeroFrame mmCorrectnessProofs venomState venomMemDefs stateEquiv

Theorem remaining_frame_oracle_updates[simp]:
  copy_fwd_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    copy_fwd_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  icf_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    icf_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  dse_frame space (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    dse_frame space s with <| vs_outcomes := os; vs_requests := rqs |> /\
  dse_all_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    dse_all_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  m2v_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    m2v_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  memzero_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    memzero_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  Cases_on `space` >> simp[copy_fwd_frame_def, icf_frame_def,
    dse_frame_def, dse_all_frame_def, m2v_frame_def, memzero_frame_def]
QED

(* Auxiliary memory/allocation predicates do not inspect either list. *)
Theorem m2v_memory_oracle_updates[simp]:
  in_promoted_region fn (s with <| vs_outcomes := os; vs_requests := rqs |>) i =
    in_promoted_region fn s i /\
  mem_byte i (s with <| vs_outcomes := os; vs_requests := rqs |>) = mem_byte i s /\
  allocas_non_overlapping (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    allocas_non_overlapping s /\
  mload a (s with <| vs_outcomes := os; vs_requests := rqs |>) = mload a s
Proof
  simp[in_promoted_region_def, mem_byte_def, allocas_non_overlapping_def,
       mload_def]
QED

Theorem copy_fwd_rel_oracle_same_updates:
  copy_fwd_rel dst src sz s1 s2 ==>
  copy_fwd_rel dst src sz
    (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[copy_fwd_rel_def, observable_equiv_def, lookup_var_def,
       copy_fwd_frame_def, venom_state_component_equality]
QED

Theorem icf_equiv_oracle_same_updates:
  icf_equiv s1 s2 ==>
  icf_equiv (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[icf_equiv_def, lookup_var_def, icf_frame_def, venom_state_component_equality]
QED

Theorem dse_equiv_oracle_same_updates:
  dse_equiv space s1 s2 ==>
  dse_equiv space (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  Cases_on `space` >> simp[dse_equiv_def, lookup_var_def,
       dse_frame_def, venom_state_component_equality]
QED

Theorem dse_all_equiv_oracle_same_updates:
  dse_all_equiv s1 s2 ==>
  dse_all_equiv (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[dse_all_equiv_def, lookup_var_def, dse_all_frame_def,
       venom_state_component_equality]
QED

Theorem m2v_equiv_oracle_same_updates:
  m2v_equiv vars s1 s2 ==>
  m2v_equiv vars (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[m2v_equiv_def, lookup_var_def, m2v_frame_def, venom_state_component_equality]
QED

Theorem m2v_inv_noix_oracle_same_updates:
  m2v_inv_noix fn s1 s2 ==>
  m2v_inv_noix fn (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[m2v_inv_noix_def, lookup_var_def, m2v_frame_def,
       venom_state_component_equality] >> strip_tac >> gvs[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem memzero_inv_oracle_same_updates:
  memzero_inv fresh s1 s2 ==>
  memzero_inv fresh (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[memzero_inv_def, lookup_var_def, memzero_frame_def,
       venom_state_component_equality]
QED

Theorem R_dse_ok_oracle_same_updates:
  R_dse_ok space s1 s2 ==>
  R_dse_ok space (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[R_dse_ok_def] >> metis_tac[dse_equiv_oracle_same_updates]
QED

Theorem m2v_inv_oracle_same_updates:
  m2v_inv fn s1 s2 ==>
  m2v_inv fn (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[m2v_inv_def, lookup_var_def] >> metis_tac[m2v_equiv_oracle_same_updates]
QED

(* Exact independent-payload iff, not an extra assumption on constructors. *)
Theorem copy_fwd_rel_oracle_updates:
  copy_fwd_rel dst src sz
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  copy_fwd_rel dst src sz
    (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule copy_fwd_rel_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem icf_equiv_oracle_updates:
  icf_equiv (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  icf_equiv (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule icf_equiv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem dse_equiv_oracle_updates:
  dse_equiv space (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  dse_equiv space (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule dse_equiv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem dse_all_equiv_oracle_updates:
  dse_all_equiv (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  dse_all_equiv (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule dse_all_equiv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem m2v_equiv_oracle_updates:
  m2v_equiv vars (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  m2v_equiv vars (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule m2v_equiv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem m2v_inv_noix_oracle_updates:
  m2v_inv_noix fn (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  m2v_inv_noix fn (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule m2v_inv_noix_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem memzero_inv_oracle_updates:
  memzero_inv fresh (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  memzero_inv fresh (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule memzero_inv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem R_dse_ok_oracle_updates:
  R_dse_ok space (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  R_dse_ok space (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule R_dse_ok_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem m2v_inv_oracle_updates:
  m2v_inv fn (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  m2v_inv fn (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac >- (strip_tac >> drule m2v_inv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED
