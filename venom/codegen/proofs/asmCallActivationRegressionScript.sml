(* TASK041 focused live-dispatch checks. Expected records retain all other
 * fields, including context, gas readings, and the suffix below a short write.
 * Computed arithmetic is delegated to the shared oracle's saved contracts. *)
Theory asmCallActivationRegression
Ancestors
  asmSem asmCallOracleProps asmOracleRegression extCallOracle venomState
  list rich_list pair words

Theorem ordinary_address_eight[simp]:
  (8w:address) <> 1w /\ (8w:address) <> 2w /\
  (8w:address) <> 6w /\ (8w:address) <> 7w
Proof
  wordsLib.WORD_DECIDE_TAC
QED

(* Gas must still occupy a stack slot; activation never supplies a missing
 * operand or turns malformed stacks into ordinary oracle requests. *)
Theorem call_staticcall_stack_underflow:
  asm_step lo otp (AsmOp "CALL") (s with as_stack := []) =
    AsmError "call: stack underflow" /\
  asm_step lo otp (AsmOp "STATICCALL") (s with as_stack := []) =
    AsmError "staticcall: stack underflow"
Proof
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def]
QED

Theorem call_ordinary_success:
  s.as_outcomes = outcome::rest /\ outcome.co_success /\
  ~s.as_call_ctx.cc_static ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [1w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 F];
    as_accounts := outcome.co_accounts; as_transient := outcome.co_tStorage;
    as_logs := s.as_logs ++ outcome.co_logs;
    as_returndata := outcome.co_returnData |>))
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

Theorem call_ordinary_failure:
  s.as_outcomes = outcome::rest /\ ~outcome.co_success ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 F];
    as_returndata := outcome.co_returnData |>))
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

Theorem call_inherits_staticness:
  s.as_outcomes = outcome::rest /\ outcome.co_success /\
  s.as_call_ctx.cc_static ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [1w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 F];
    as_returndata := outcome.co_returnData |>)) /\
  (asm_call_request s 8w 0w 0 0 F).cr_static
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

Theorem staticcall_success_zero_value:
  s.as_outcomes = outcome::rest /\ outcome.co_success ==>
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [1w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 T];
    as_returndata := outcome.co_returnData |>)) /\
  (asm_call_request s 8w 0w 0 0 T).cr_value = 0 /\
  (asm_call_request s 8w 0w 0 0 T).cr_static
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

Theorem call_and_staticcall_exhaustion:
  s.as_outcomes = [] ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_requests := s.as_requests ++
      [asm_call_request s 8w 0w 0 0 F]; as_returndata := [] |>)) /\
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_requests := s.as_requests ++
      [asm_call_request s 8w 0w 0 0 T]; as_returndata := [] |>))
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, failed_outcome_def, asm_next_def,
       asm_state_component_equality]
QED

Theorem computed_empty_ecrecover_dispatch:
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 1w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [1w]; as_returndata := [] |>)) /\
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 1w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [1w]; as_returndata := [] |>))
Proof
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       precompile_result_empty_ecrecover, failed_outcome_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

(* Concrete short write: two returned bytes at 2, requested size 8. The
 * unchanged suffix starts at 4, NOT at 10; memory still has length 32. *)
Theorem call_staticcall_short_write:
  s.as_memory = REPLICATE 32 (9w:byte) /\
  s.as_outcomes = outcome::rest /\ outcome.co_returnData = [77w; 88w] /\
  ~outcome.co_success ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 0w; 2w; 8w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 F];
    as_returndata := [77w; 88w];
    as_memory := REPLICATE 2 9w ++ [77w; 88w] ++ REPLICATE 28 9w |>)) /\
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 8w; 0w; 0w; 2w; 8w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 8w 0w 0 0 T];
    as_returndata := [77w; 88w];
    as_memory := REPLICATE 2 9w ++ [77w; 88w] ++ REPLICATE 28 9w |>))
Proof
  strip_tac >> conj_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_next_def] >>
  simp[asm_call_request_def, asm_expand_memory_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, REPLICATE, asm_state_component_equality] >> EVAL_TAC
QED

Theorem gas_live_readings_and_exhaustion:
  asm_step lo otp (AsmOp "GAS") (s with as_gas_readings := a::b::rest) =
    AsmOK (asm_next (s with <| as_stack := a::s.as_stack;
                              as_gas_readings := b::rest |>)) /\
  asm_step lo otp (AsmOp "GAS") (s with as_gas_readings := []) =
    AsmOK (asm_next (s with <| as_stack := 0w::s.as_stack;
                              as_gas_readings := [] |>))
Proof
  simp[asm_step_call_staticcall_gas, asm_gas_def, asm_push_val_def, asm_next_def]
QED

Theorem gas_reading_not_call_context:
  asm_step lo otp (AsmOp "GAS")
    (s with <| as_gas_readings := [37w];
               as_call_ctx := s.as_call_ctx with cc_gas := 999 |>) =
  AsmOK (asm_next (s with <|
    as_stack := 37w::s.as_stack; as_gas_readings := [];
    as_call_ctx := s.as_call_ctx with cc_gas := 999 |>))
Proof
  simp[asm_step_call_staticcall_gas, asm_gas_def, asm_push_val_def, asm_next_def]
QED

Theorem call_request_input_padding:
  (asm_call_request (s with as_memory := [9w]) 8w 4w 0 3 F).cr_data =
    [9w; 0w; 0w] /\
  (asm_call_request s 8w 4w 0 0 F).cr_accounts = s.as_accounts /\
  (asm_call_request s 8w 4w 0 0 F).cr_tStorage = s.as_transient
Proof
  simp[asm_call_request_def, asm_expand_memory_def] >> EVAL_TAC
QED

Theorem computed_sha256_and_ec_dispatch:
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 2w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [1w];
    as_returndata := word_to_bytes
      (0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855w:bytes32) T |>)) /\
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 6w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [1w];
                            as_returndata := REPLICATE 64 0w |>)) /\
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 7w; 0w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [1w];
                            as_returndata := REPLICATE 64 0w |>))
Proof
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       precompile_result_empty_sha256, precompile_result_empty_ec,
       failed_outcome_def, adopt_outcome_def, asm_next_def,
       asm_state_component_equality]
QED

Theorem asm_invalid_ec_request[local]:
  s.as_memory = REPLICATE 63 0w ++ [1w] /\ (addr = 6w \/ addr = 7w) ==>
  take_outcome (asm_call_request s addr 0w 0 64 static) os =
    (failed_outcome (asm_call_request s addr 0w 0 64 static),os) /\
  record_request (asm_call_request s addr 0w 0 64 static) rqs = rqs
Proof
  strip_tac >> irule take_outcome_invalid_ec >>
  simp[asm_call_request_def, asm_expand_memory_def, TAKE_LENGTH_TOO_LONG]
QED

Theorem computed_invalid_ec_dispatch:
  s.as_memory = REPLICATE 63 (0w:byte) ++ [1w] ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 6w; 0w; 0w; 64w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [0w]; as_returndata := [] |>)) /\
  asm_step lo otp (AsmOp "STATICCALL")
    (s with as_stack := [gas; 7w; 0w; 64w; 0w; 0w]) =
  AsmOK (asm_next (s with <| as_stack := [0w]; as_returndata := [] |>))
Proof
  strip_tac >> conj_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def, asm_exec_staticcall_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_next_def] >>
  simp[asm_invalid_ec_request, failed_outcome_fields] >>
  simp[adopt_outcome_def, failed_outcome_def, asm_call_request_def,
       asm_expand_memory_def, TAKE_LENGTH_TOO_LONG, asm_state_component_equality]
QED

Theorem nonzero_value_precompile_shaped_call:
  s.as_outcomes = outcome::rest /\ ~outcome.co_success ==>
  asm_step lo otp (AsmOp "CALL")
    (s with as_stack := [gas; 1w; 9w; 0w; 0w; 0w; 0w]) =
  AsmOK (asm_next (s with <|
    as_stack := [0w]; as_outcomes := rest;
    as_requests := s.as_requests ++ [asm_call_request s 1w 9w 0 0 F];
    as_returndata := outcome.co_returnData |>))
Proof
  strip_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_call_def,
       asm_consume_call_outcome_eq, asm_call_memory_def, asm_call_request_def,
       computed_precompile_addresses, take_outcome_def, record_request_def,
       adopt_outcome_def, asm_next_def, asm_state_component_equality]
QED

Theorem call_zero_size_does_not_expand:
  asm_call_memory 12345 0 54321 0 mem = mem
Proof
  simp[asm_call_memory_def]
QED

Theorem short_write_keeps_length_and_suffix:
  LENGTH (REPLICATE 2 (9w:byte) ++ [77w;88w] ++ REPLICATE 28 9w) = 32 /\
  DROP 4 (REPLICATE 2 (9w:byte) ++ [77w;88w] ++ REPLICATE 28 9w) =
    DROP 4 (REPLICATE 32 9w)
Proof
  mp_tac (overwrite_prefix_length_suffix |> INST_TYPE [alpha |-> ``:byte``]
    |> Q.INST [`off` |-> `2`, `bytes` |-> `[77w;88w]:byte list`,
               `mem` |-> `REPLICATE 32 (9w:byte)`]) >>
  simp[DROP_REPLICATE] >> EVAL_TAC
QED

Theorem gas_three_steps:
  asm_steps lo otp [AsmOp "GAS"; AsmOp "GAS"; AsmOp "GAS"] 3
    (s with <| as_pc := 0; as_gas_readings := [13w;21w] |>) =
  AsmOK (s with <| as_pc := 3; as_gas_readings := [];
                  as_stack := 0w::21w::13w::s.as_stack |> )
Proof
  rewrite_tac[DECIDE ``3 = SUC (SUC (SUC 0))``] >>
  simp[Once asm_steps_def, asm_step_call_staticcall_gas,
       asm_gas_def, asm_push_val_def, asm_next_def] >>
  rewrite_tac[DECIDE ``2 = SUC (SUC 0)``] >>
  simp[Once asm_steps_def, asm_step_call_staticcall_gas,
       asm_gas_def, asm_push_val_def, asm_next_def] >>
  rewrite_tac[DECIDE ``1 = SUC 0``] >>
  simp[Once asm_steps_def, asm_step_call_staticcall_gas,
       asm_gas_def, asm_push_val_def, asm_next_def] >> simp[asm_steps_def]
QED
