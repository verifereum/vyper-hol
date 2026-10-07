(* TASK040 prerequisite: paired request/outcome transport, NOT activation.
 * TOP-LEVEL: request agreement from actual call inputs; oracle transport;
 * residual-frame commutation/transport; static/failed adoption.
 * No unconditional primitive-oracle preservation is used or claimed.
 *)
Theory venomCallOracleProps
Ancestors
  venomCallOracleDefs venomState extCallOracle stateFrame
  arithmetic list pair words

(* Exact input agreement, not a new observability hypothesis on a pass.
 * Memory may differ outside the calldata slice; gas is not an input.
 *)
Theorem venom_call_request_agreement:
  w2w addr1 = (w2w addr2 : address) /\ value1 = value2 /\
  read_memory (w2n ao1) (w2n sz1) s1 =
    read_memory (w2n ao2) (w2n sz2) s2 /\
  (static1 \/ s1.vs_call_ctx.cc_static) =
    (static2 \/ s2.vs_call_ctx.cc_static) /\
  s1.vs_accounts = s2.vs_accounts /\ s1.vs_transient = s2.vs_transient ==>
  venom_call_request s1 addr1 value1 ao1 sz1 static1 =
    venom_call_request s2 addr2 value2 ao2 sz2 static2
Proof
  simp[venom_call_request_def]
QED

Theorem venom_call_request_frame[simp]:
  venom_call_request (state_frame s) addr value ao sz st =
    venom_call_request s addr value ao sz st /\
  venom_call_request (execution_frame s) addr value ao sz st =
    venom_call_request s addr value ao sz st
Proof
  simp[venom_call_request_def, read_memory_def,
       state_frame_def, execution_frame_def]
QED

(* This single tuple boundary is enough for all relation families. Neither
 * accounts/logs nor memory agreement is needed to transport these outputs.
 *)
Theorem consume_call_outcome_observation:
  (FST (consume_call_outcome rq ro rs s),
   (SND (consume_call_outcome rq ro rs s)).vs_outcomes,
   (SND (consume_call_outcome rq ro rs s)).vs_requests) =
  (if (FST (take_outcome rq s.vs_outcomes)).co_success then 1w else 0w,
   SND (take_outcome rq s.vs_outcomes), record_request rq s.vs_requests)
Proof
  simp[consume_call_outcome_def] >>
  Cases_on `take_outcome rq s.vs_outcomes` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem consume_call_outcome_oracle_transport:
  rq1 = rq2 /\ s1.vs_outcomes = s2.vs_outcomes /\
  s1.vs_requests = s2.vs_requests ==>
  FST (consume_call_outcome rq1 ro1 rs1 s1) =
    FST (consume_call_outcome rq2 ro2 rs2 s2) /\
  (SND (consume_call_outcome rq1 ro1 rs1 s1)).vs_outcomes =
    (SND (consume_call_outcome rq2 ro2 rs2 s2)).vs_outcomes /\
  (SND (consume_call_outcome rq1 ro1 rs1 s1)).vs_requests =
    (SND (consume_call_outcome rq2 ro2 rs2 s2)).vs_requests
Proof
  metis_tac[consume_call_outcome_observation, PAIR_EQ]
QED

Theorem consume_call_outcome_frame:
  consume_call_outcome rq ro rs (state_frame s) =
    (FST (consume_call_outcome rq ro rs s),
     state_frame (SND (consume_call_outcome rq ro rs s))) /\
  consume_call_outcome rq ro rs (execution_frame s) =
    (FST (consume_call_outcome rq ro rs s),
     execution_frame (SND (consume_call_outcome rq ro rs s)))
Proof
  simp[consume_call_outcome_def, state_frame_def, execution_frame_def,
       write_memory_with_expansion_def] >>
  Cases_on `take_outcome rq s.vs_outcomes` >> simp[] >>
  pairarg_tac >> simp[]
QED

(* Reuse the existing residual masks, not a retained-selector matrix.
 * Consumers with renamed variables/control fields need no whole-state eq.
 *)
Theorem consume_call_outcome_frame_transport:
  (state_frame s1 = state_frame s2 ==>
    state_frame (SND (consume_call_outcome rq ro rs s1)) =
    state_frame (SND (consume_call_outcome rq ro rs s2))) /\
  (execution_frame s1 = execution_frame s2 ==>
    execution_frame (SND (consume_call_outcome rq ro rs s1)) =
    execution_frame (SND (consume_call_outcome rq ro rs s2)))
Proof
  metis_tac[consume_call_outcome_frame, PAIR_EQ]
QED

Theorem consume_call_outcome_static_or_failed:
  rq.cr_static \/ ~(FST (take_outcome rq s.vs_outcomes)).co_success ==>
  (SND (consume_call_outcome rq ro rs s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rs s)).vs_transient = s.vs_transient /\
  (SND (consume_call_outcome rq ro rs s)).vs_logs = s.vs_logs
Proof
  simp[consume_call_outcome_def] >>
  Cases_on `take_outcome rq s.vs_outcomes` >> simp[] >>
  rw[adopt_outcome_def] >> simp[]
QED

(* Binding the output leaves every residual field intact, by the existing
 * generic frame_update_var. This applies equally to success and failure.
 *)
Theorem consume_call_outcome_bind_frame:
  state_frame (update_var out (FST (consume_call_outcome rq ro rs s))
    (SND (consume_call_outcome rq ro rs s))) =
    state_frame (SND (consume_call_outcome rq ro rs s)) /\
  execution_frame (update_var out (FST (consume_call_outcome rq ro rs s))
    (SND (consume_call_outcome rq ro rs s))) =
    execution_frame (SND (consume_call_outcome rq ro rs s))
Proof
  simp[]
QED
