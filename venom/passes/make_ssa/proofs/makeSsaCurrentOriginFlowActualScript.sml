Theory makeSsaCurrentOriginFlowActual
Ancestors makeSsaCurrentOriginFlow makeSsaCurrentRetainedJoint
  makeSsaCurrentCompletedBatch makeSsaCurrentJointRuntime makeSsaCurrentPhiOrigins
  makeSsaCurrentDefs list alist pair

Theorem current_origin_flow_source_batch:
  !bs M N. current_origin_flow_replay
    (MAP (\b. CurrentFlowSource (FST b) (SND b)) (REVERSE bs))
    M N (bs ++ M) N
Proof
  Induct >> simp[current_origin_flow_replay_def, current_origin_flow_replay_append] >>
  rpt strip_tac >> PairCases_on `h` >>
  qexistsl_tac [`bs ++ M`, `N`] >>
  simp[current_origin_flow_replay_def, current_flow_step_def]
QED

Theorem current_origin_flow_target_batch:
  !bs M N. current_origin_flow_replay
    (MAP (\b. CurrentFlowTarget (FST b) (SND b)) (REVERSE bs))
    M N M (bs ++ N)
Proof
  Induct >> simp[current_origin_flow_replay_def, current_origin_flow_replay_append] >>
  rpt strip_tac >> PairCases_on `h` >>
  qexistsl_tac [`M`, `bs ++ N`] >>
  simp[current_origin_flow_replay_def, current_flow_step_def]
QED

Theorem current_origin_lookup_filter:
  !bs. x <> v ==> ALOOKUP (FILTER (\b. FST b <> v) bs) x = ALOOKUP bs x
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  Cases_on `h0 = v` >> simp[] >> Cases_on `h0 = x` >> simp[]
QED

Theorem current_origin_batch_move_selected:
  ALL_DISTINCT (MAP FST bs) /\ MEM (v,origin) bs ==>
  !x. ALOOKUP ((v,origin)::(FILTER (\b. FST b <> v) bs ++ M)) x =
    ALOOKUP (bs ++ M) x
Proof
  strip_tac >>
  `ALOOKUP bs v = SOME origin` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  gen_tac >> Cases_on `x = v` >>
  simp[current_origin_lookup_filter, ALOOKUP_APPEND]
QED

Theorem current_origin_flow_batch_pair:
  ALL_DISTINCT (MAP FST bs) /\ ALL_DISTINCT (MAP FST cs) /\
  MEM (v,origin) bs /\ MEM (y,origin) cs ==>
  ?es M' N'. current_origin_flow_replay es M N M' N' /\
    (!x. ALOOKUP M' x = ALOOKUP (bs ++ M) x) /\
    (!z. ALOOKUP N' z = ALOOKUP (cs ++ N) z) /\
    current_request_pullback es (CurrentFlowPending v y) = CurrentFlowDischarged
Proof
  strip_tac >>
  qexistsl_tac [
    `MAP (\b. CurrentFlowSource (FST b) (SND b)) (REVERSE (FILTER (\b. FST b <> v) bs)) ++
     MAP (\b. CurrentFlowTarget (FST b) (SND b)) (REVERSE (FILTER (\b. FST b <> y) cs)) ++
     [CurrentFlowPair v y origin]`,
    `(v,origin)::(FILTER (\b. FST b <> v) bs ++ M)`,
    `(y,origin)::(FILTER (\b. FST b <> y) cs ++ N)`] >>
  rpt conj_tac
  >- (rewrite_tac[current_origin_flow_replay_append] >>
      qexistsl_tac [`FILTER (\b. FST b <> v) bs ++ M`,
        `FILTER (\b. FST b <> y) cs ++ N`] >>
      conj_tac
      >- (qexistsl_tac [`FILTER (\b. FST b <> v) bs ++ M`, `N`] >>
          simp[current_origin_flow_source_batch, current_origin_flow_target_batch]) >>
      simp[current_origin_flow_replay_def, current_flow_step_def])
  >- metis_tac[current_origin_batch_move_selected]
  >- metis_tac[current_origin_batch_move_selected] >>
  simp[current_request_pullback_append, current_request_pullback_def,
    current_request_step_def, current_request_pullback_absorbing]
QED

Theorem current_origin_realizes_lookup_cong:
  (!x. ALOOKUP M' x = ALOOKUP M x) ==>
  (current_origin_realizes V M' st <=> current_origin_realizes V M st)
Proof
  simp[current_origin_realizes_def]
QED

Theorem current_origin_flow_retained_batch:
  current_joint_rel V M N rs D st st' /\ MEM v D /\
  st.vs_prev_bb = SOME p /\ inst.inst_opcode = PHI /\ inst_wf inst /\
  resolve_phi p inst.inst_operands = SOME (Var v) /\
  eval_one_phi st inst = SOME (dst,value) /\
  target.inst_outputs = [name] /\
  resolve_phi p target.inst_operands = SOME (Var (latest_current_name rs v)) /\
  LIST_REL (current_phi_origin_read M p) prefix bs /\ MEM inst prefix /\
  LIST_REL (current_phi_origin_read N p) targets cs /\ MEM target targets /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) targets)) ==>
  ?origin es M' N'. V origin = SOME value /\
    current_phi_origin_read M p inst (dst,origin) /\
    current_phi_origin_read N p target (name,origin) /\
    eval_one_phi st' target = SOME (name,value) /\
    current_origin_flow_replay es M N M' N' /\
    (!x. ALOOKUP M' x = ALOOKUP (bs ++ M) x) /\
    (!z. ALOOKUP N' z = ALOOKUP (cs ++ N) z) /\
    current_request_pullback es (CurrentFlowPending dst name) = CurrentFlowDischarged
Proof
  strip_tac >> drule_all current_joint_selected_phi_success >> strip_tac >>
  `MEM (dst,origin) bs /\ MEM (name,origin) cs` by
    metis_tac[current_phi_origin_binding_member] >>
  `ALL_DISTINCT (MAP FST bs) /\ ALL_DISTINCT (MAP FST cs)` by
    metis_tac[current_phi_origin_binding_outputs] >>
  qexists `origin` >> simp[] >>
  irule current_origin_flow_batch_pair >> simp[] >> metis_tac[]
QED
