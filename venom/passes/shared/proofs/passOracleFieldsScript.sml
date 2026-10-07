(* TASK037: actual residual-frame oracle coverage. Definitions stay unchanged.
 * TOP-LEVEL: projections/coverage, arbitrary paired constructors, primitive
 * and setup/merge transport. Memory/region/displacement/FMP contracts remain.
 * Reuses TASK035 primitive commutation and callee projection boundaries. *)
Theory passOracleFields
Ancestors
  passResidualFrame passSharedFrame allocaRemapDefs concretizeMemLocProofs
  venomState venomExecSemantics oracleExecProps oracleStateProps calleeTransport
  stateEquiv passSimulationDefs passSimulationProps passSharedDefs venomMemDefs

(* ===== Both actual lists survive canonicalization ===== *)

Theorem pass_frame_oracle[simp]:
  (commute_frame s).vs_outcomes = s.vs_outcomes /\
  (commute_frame s).vs_requests = s.vs_requests /\
  (alloca_remap_frame s).vs_outcomes = s.vs_outcomes /\
  (alloca_remap_frame s).vs_requests = s.vs_requests /\
  (concretize_frame s).vs_outcomes = s.vs_outcomes /\
  (concretize_frame s).vs_requests = s.vs_requests
Proof
  simp[commute_frame_def, alloca_remap_frame_def, concretize_frame_def]
QED

Theorem pass_frame_oracle_transport:
  (commute_frame s1 = commute_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (alloca_remap_frame s1 = alloca_remap_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (concretize_frame s1 = concretize_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac
  >- (strip_tac >> conj_tac >> irule commute_frame_projection >>
      simp_tac bool_ss [pass_frame_oracle] >> metis_tac[]) >>
  conj_tac
  >- (strip_tac >> conj_tac >> irule alloca_remap_frame_projection >>
      simp_tac bool_ss [pass_frame_oracle] >> metis_tac[]) >>
  strip_tac >> conj_tac >> irule concretize_frame_projection >>
  simp_tac bool_ss [pass_frame_oracle] >> metis_tac[]
QED

Theorem pass_frame_oracle_updates[simp]:
  commute_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    commute_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  alloca_remap_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    alloca_remap_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  concretize_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    concretize_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[commute_frame_def, alloca_remap_frame_def, concretize_frame_def]
QED

(* FIRST kernel audit: no redundant selector conjuncts are needed. *)
Theorem commute_equiv_oracle:
  commute_equiv vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 1 pass_frame_oracle_transport) >>
  fs[commute_equiv_def]
QED

Theorem alloca_remap_rel_oracle:
  alloca_remap_rel fn roots remap s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 2 pass_frame_oracle_transport) >>
  fs[alloca_remap_rel_def, LET_THM]
QED

Theorem concretize_rel_oracle:
  concretize_rel amap fn livesets init s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 3 pass_frame_oracle_transport) >>
  fs[concretize_rel_def, LET_THM]
QED

Theorem pass_relations_oracle_coverage:
  (commute_equiv vars s1 s2 <=>
    commute_equiv vars s1 s2 /\ s1.vs_outcomes = s2.vs_outcomes /\
    s1.vs_requests = s2.vs_requests) /\
  (alloca_remap_rel fn roots remap s1 s2 <=>
    alloca_remap_rel fn roots remap s1 s2 /\ s1.vs_outcomes = s2.vs_outcomes /\
    s1.vs_requests = s2.vs_requests) /\
  (concretize_rel amap fn livesets init s1 s2 <=>
    concretize_rel amap fn livesets init s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  metis_tac[commute_equiv_oracle, alloca_remap_rel_oracle, concretize_rel_oracle]
QED

(* ===== Exact setup/merge commutation, with arbitrary payloads ===== *)

Theorem pass_call_oracle_updates:
  setup_callee fn args (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    OPTION_MAP (\c. c with <| vs_outcomes := os; vs_requests := rqs |>)
      (setup_callee fn args s) /\
  merge_callee_state
    (caller with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (callee with <| vs_outcomes := os2; vs_requests := rqs2 |>) =
    merge_callee_state caller callee
      with <| vs_outcomes := os2; vs_requests := rqs2 |>
Proof
  simp[setup_callee_def, merge_callee_state_def] >>
  Cases_on `NULL fn.fn_blocks` >> simp[]
QED

Theorem commute_equiv_oracle_refl:
  commute_equiv vars s s
Proof
  simp[commute_equiv_def]
QED

(* ===== Unchanged allocation/memory contracts ===== *)

Theorem alloca_oracle_updates[simp]:
  alloca_mem_agrees remap
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) =
    alloca_mem_agrees remap s1 s2 /\
  in_alloca_region (s with <| vs_outcomes := os; vs_requests := rqs |>) i =
    in_alloca_region s i /\
  allocas_non_overlapping (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    allocas_non_overlapping s /\
  allocas_in_memory (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    allocas_in_memory s
Proof
  simp[alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def, allocas_in_memory_def]
QED

(* Exact constructor iff for arbitrary payloads, preserving every old clause. *)
Theorem commute_equiv_oracle_updates:
  commute_equiv vars
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  commute_equiv vars
    (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac
  >- (strip_tac >> drule commute_equiv_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem commute_equiv_oracle_same_updates:
  commute_equiv vars s1 s2 ==>
  commute_equiv vars
    (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[commute_equiv_def, lookup_var_def, commute_frame_def,
       venom_state_component_equality]
QED

(* Successful steps project the existing full paired result relation. *)
Theorem commute_equiv_step_oracle:
  lift_result (commute_equiv vars) (commute_equiv vars) (commute_equiv vars)
    (step_inst_base inst1 s1) (step_inst_base inst2 s2) /\
  step_inst_base inst1 s1 = OK t1 /\ step_inst_base inst2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  (* Legacy preservation: metis_tac[commute_equiv_oracle, step_inst_base_oracle] *)
  strip_tac >> gvs[lift_result_def] >> metis_tac[commute_equiv_oracle]
QED

(* All four state-bearing constructors; Error is state-free as before. *)
Theorem commute_equiv_lift_result_oracle:
  lift_result (commute_equiv vars) (commute_equiv vars) (commute_equiv vars) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[commute_equiv_oracle]
QED

(* Exact constructor iff for arbitrary payloads, preserving every old clause. *)
Theorem alloca_remap_rel_oracle_updates:
  alloca_remap_rel fn roots remap
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  alloca_remap_rel fn roots remap
    (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac
  >- (strip_tac >> drule alloca_remap_rel_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem alloca_remap_rel_oracle_same_updates:
  alloca_remap_rel fn roots remap s1 s2 ==>
  alloca_remap_rel fn roots remap
    (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[alloca_remap_rel_def, LET_THM, lookup_var_def, alloca_remap_frame_def,
       venom_state_component_equality]
QED

(* Successful steps project the existing full paired result relation. *)
Theorem alloca_remap_rel_step_oracle:
  lift_result (alloca_remap_rel fn roots remap)
    (alloca_remap_rel fn roots remap) (alloca_remap_rel fn roots remap)
    (step_inst_base inst1 s1) (step_inst_base inst2 s2) /\
  step_inst_base inst1 s1 = OK t1 /\ step_inst_base inst2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  (* Legacy preservation: metis_tac[alloca_remap_rel_oracle, step_inst_base_oracle] *)
  strip_tac >> gvs[lift_result_def] >> metis_tac[alloca_remap_rel_oracle]
QED

(* All four state-bearing constructors; Error is state-free as before. *)
Theorem alloca_remap_rel_lift_result_oracle:
  lift_result (alloca_remap_rel fn roots remap)
    (alloca_remap_rel fn roots remap) (alloca_remap_rel fn roots remap) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[alloca_remap_rel_oracle]
QED

(* Exact constructor iff for arbitrary payloads, preserving every old clause. *)
Theorem concretize_rel_oracle_updates:
  concretize_rel amap fn livesets init
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  concretize_rel amap fn livesets init
    (s1 with <| vs_outcomes := os2; vs_requests := rqs2 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) /\
  os1 = os2 /\ rqs1 = rqs2
Proof
  eq_tac
  >- (strip_tac >> drule concretize_rel_oracle >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem concretize_rel_oracle_same_updates:
  concretize_rel amap fn livesets init s1 s2 ==>
  concretize_rel amap fn livesets init
    (s1 with <| vs_outcomes := os; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os; vs_requests := rqs |>)
Proof
  simp[concretize_rel_def, LET_THM, lookup_var_def, concretize_frame_def,
       venom_state_component_equality] >> strip_tac >> gvs[]
QED

(* Successful steps project the existing full paired result relation. *)
Theorem concretize_rel_step_oracle:
  lift_result (concretize_rel amap fn livesets init)
    (concretize_rel amap fn livesets init) (concretize_rel amap fn livesets init)
    (step_inst_base inst1 s1) (step_inst_base inst2 s2) /\
  step_inst_base inst1 s1 = OK t1 /\ step_inst_base inst2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  (* Legacy preservation: metis_tac[concretize_rel_oracle, step_inst_base_oracle] *)
  strip_tac >> gvs[lift_result_def] >> metis_tac[concretize_rel_oracle]
QED

(* All four state-bearing constructors; Error is state-free as before. *)
Theorem concretize_rel_lift_result_oracle:
  lift_result (concretize_rel amap fn livesets init)
    (concretize_rel amap fn livesets init)
    (concretize_rel amap fn livesets init) r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
    r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >>
  metis_tac[concretize_rel_oracle]
QED

(* ===== Paired setup/merge transport from TASK035 callee boundaries ===== *)

Theorem commute_equiv_callee_oracle:
  commute_equiv vars s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[commute_equiv_oracle, setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem alloca_remap_rel_callee_oracle:
  alloca_remap_rel fn roots remap s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[alloca_remap_rel_oracle, setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem concretize_rel_callee_oracle:
  concretize_rel amap fn livesets init s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[concretize_rel_oracle, setup_callee_oracle, merge_callee_state_oracle]
QED
