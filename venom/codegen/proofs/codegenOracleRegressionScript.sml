(* Relation-local oracle regressions. No trace-aware EVM simulation claim. *)
Theory codegenOracleRegression
Ancestors
  codegenRel contextCodegenRel asmSem asmOracleRegression venomState
  venomCallOracleDefs venomCallOracleProps venomCallActivationRegression
  asmCallOracleProps asmCallActivationRegression venomExecSemantics
  stackPlanGen stackPlanTypes extCallOracle finite_map list rich_list

(* Closed witness for the obsolete four-field terminal constructor: its
   premises hold, but it cannot establish observable request equality. *)
Theorem terminal_constructor_missing_requests_counterexample:
  let vs = init_venom_state "entry" in
  let as1 = asm_oracle_initial with as_requests :=
    [venom_call_request vs 8w 0w 0w 0w F] in
    as1.as_accounts = vs.vs_accounts /\
    as1.as_transient = vs.vs_transient /\
    as1.as_returndata = vs.vs_returndata /\
    as1.as_logs = vs.vs_logs /\
    ~venom_asm_terminal_rel vs as1
Proof
  simp[init_venom_state_def, asm_oracle_initial_def,
       venom_asm_terminal_rel_def]
QED

(* The planned running substrate accepts arbitrary assembly readings, but
   rejects either shared-list mismatch. Context and function-local relations
   agree on these oracle fields even with an empty context spill mask. *)
Theorem running_oracle_and_gas_boundary:
  let vs = init_venom_state "entry" in
  let as1 = asm_oracle_initial with as_gas_readings := readings in
  let rq = venom_call_request vs 8w 0w 0w 0w F in
    venom_asm_rel FEMPTY (init_plan_state 0) vs as1 /\
    context_venom_asm_rel cp FEMPTY (init_plan_state 0) vs as1 /\
    ~venom_asm_rel FEMPTY (init_plan_state 0) vs
      (as1 with as_outcomes := [failed_outcome rq]) /\
    ~venom_asm_rel FEMPTY (init_plan_state 0) vs
      (as1 with as_requests := [rq]) /\
    ~context_venom_asm_rel cp FEMPTY (init_plan_state 0) vs
      (as1 with as_outcomes := [failed_outcome rq]) /\
    ~context_venom_asm_rel cp FEMPTY (init_plan_state 0) vs
      (as1 with as_requests := [rq])
Proof
  simp[init_venom_state_def, asm_oracle_initial_def, init_plan_state_def,
       venom_asm_rel_def, context_venom_asm_rel_def, plan_stack_rel_def,
       plan_spill_rel_def, FLOOKUP_DEF, memory_rel_def, context_memory_rel_def]
QED

(* Deliberately no terminal leftover-outcome or GAS-reading equality. *)
Theorem terminal_leftovers_and_readings_free:
  venom_asm_terminal_rel vs
    (s with <| as_outcomes := outcomes; as_gas_readings := readings |>) =
  venom_asm_terminal_rel vs s
Proof
  simp[venom_asm_terminal_rel_def]
QED

(* Both actual request builders read the same nonempty, zero-padded input
   and apply opcode OR inherited staticness. No forwarded GAS value enters. *)
Theorem actual_request_builders_padding_staticness:
  let vs = (init_venom_state "entry") with <|
    vs_memory := [11w; 22w];
    vs_call_ctx := empty_call_context with cc_static := inherited |>
  in
  let as1 = asm_oracle_initial with <|
    as_memory := [11w; 22w];
    as_call_ctx := empty_call_context with cc_static := inherited |>
  in
    asm_call_request as1 8w 7w 1 3 opcode_static =
      venom_call_request vs 8w 7w 1w 3w opcode_static /\
    (asm_call_request as1 8w 7w 1 3 opcode_static).cr_data = [22w; 0w; 0w] /\
    (asm_call_request as1 8w 7w 1 3 opcode_static).cr_static =
      (opcode_static \/ inherited)
Proof
  simp[asm_call_request_def, venom_call_request_def,
       init_venom_state_def, asm_oracle_initial_def, read_memory_def,
       asm_expand_memory_def, expand_memory_def, empty_call_context_def,
       TAKE_APPEND, DROP_APPEND, REPLICATE, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC
QED
