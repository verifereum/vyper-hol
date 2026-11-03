Theory frameViewCall
Ancestors
  frameViewFacts frameViewMemory frameViewWrite frameRel venomState
  venomExecSemantics venomCallOracleDefs contextCodegenRel codegenRel list

Theorem venom_call_request_frame_view:
  read_memory (w2n argsOff) (w2n argsSize)
    (s with vs_memory := m) = read_memory (w2n argsOff) (w2n argsSize) s ==>
  venom_call_request (frame_view fn ra s with vs_memory := m)
    addr value argsOff argsSize is_static =
  venom_call_request s addr value argsOff argsSize is_static
Proof
  simp[venom_call_request_def, read_memory_def, frame_view_def]
QED

Theorem make_venom_delegatecall_state_frame_view:
  make_venom_delegatecall_state (frame_view fn ra s with vs_memory := m)
    target gas calldata code is_static =
  make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def, frame_view_def]
QED

Theorem make_venom_create_state_frame_view:
  make_venom_create_state (frame_view fn ra s with vs_memory := m)
    addr gas value init_code =
  make_venom_create_state s addr gas value init_code
Proof
  simp[make_venom_create_state_def, venom_to_tx_params_def, frame_view_def]
QED

Theorem consume_call_outcome_frame_view:
  consume_call_outcome rq ro rs (frame_view fn ra s with vs_memory := m) =
  (FST (consume_call_outcome rq ro rs s),
   frame_view fn ra (SND (consume_call_outcome rq ro rs s)) with
     vs_memory := (SND (consume_call_outcome rq ro rs
                         (s with vs_memory := m))).vs_memory)
Proof
  simp[consume_call_outcome_eq, frame_view_def,
       write_memory_with_expansion_def]
QED

Theorem consume_call_outcome_byte_agreement:
  read_byte i m = read_byte i s.vs_memory ==>
  read_byte i (SND (consume_call_outcome rq ro rs
                     (s with vs_memory := m))).vs_memory =
  read_byte i (SND (consume_call_outcome rq ro rs s)).vs_memory
Proof
  simp[consume_call_outcome_eq, write_memory_byte_agreement]
QED

Theorem consume_call_outcome_byte_frame:
  ~(ro <= i /\ i < ro + rs) ==>
  read_byte i (SND (consume_call_outcome rq ro rs
                     (s with vs_memory := m))).vs_memory = read_byte i m
Proof
  strip_tac >>
  simp[consume_call_outcome_eq, read_byte_write_memory_with_expansion] >>
  IF_CASES_TAC >> gvs[LENGTH_TAKE_EQ]
QED

Theorem extract_venom_result_frame_view:
  extract_venom_result s output ro rs result = SOME (w, t) ==>
  extract_venom_result (frame_view fn ra s with vs_memory := m)
    output ro rs result =
  SOME (w, frame_view fn ra t with
    vs_memory := (write_memory_with_expansion ro
      (TAKE rs t.vs_returndata) (s with vs_memory := m)).vs_memory)
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> fs[frame_view_def] >> gvs[] >>
  simp[write_memory_with_expansion_def]
QED

Theorem exec_ext_call_frame_view:
  ~retpc_var fn out /\ inst.inst_outputs = [out] /\
  read_memory (w2n argsOff) (w2n argsSize) (s with vs_memory := m) =
    read_memory (w2n argsOff) (w2n argsSize) s ==>
  exec_ext_call inst (frame_view fn ra s with vs_memory := m)
    gas addr value argsOff argsSize retOff retSize is_static =
  OK (frame_view fn ra
    (update_var out
      (FST (consume_call_outcome
        (venom_call_request s addr value argsOff argsSize is_static)
        (w2n retOff) (w2n retSize) s))
      (SND (consume_call_outcome
        (venom_call_request s addr value argsOff argsSize is_static)
        (w2n retOff) (w2n retSize) s))) with
    vs_memory := (SND (consume_call_outcome
      (venom_call_request s addr value argsOff argsSize is_static)
      (w2n retOff) (w2n retSize) (s with vs_memory := m))).vs_memory)
Proof
  strip_tac >>
  drule venom_call_request_frame_view >> strip_tac >>
  simp[exec_ext_call_def, consume_call_outcome_frame_view,
       frame_view_update_var, update_var_def]
QED
