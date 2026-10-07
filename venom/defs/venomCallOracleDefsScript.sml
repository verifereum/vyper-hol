(* TASK040 prerequisite: reusable request/completion plumbing, NOT activation.
 * No opcode dispatch or concrete EVM helper is changed by this theory.
 * TOP-LEVEL: venom_call_request (already-evaluated operands),
 * consume_call_outcome (success word and state, before output binding).
 * Gas evaluation and single-output validation remain the dispatcher's job.
 *)
Theory venomCallOracleDefs
Ancestors
  venomState extCallOracle

Definition venom_call_request_def:
  venom_call_request s (addr:bytes32) (value:bytes32)
                     (argsOff:bytes32) (argsSize:bytes32) is_static =
    <| cr_target := w2w addr;
       cr_value := w2n value;
       cr_data := read_memory (w2n argsOff) (w2n argsSize) s;
       cr_static := (is_static \/ s.vs_call_ctx.cc_static);
       cr_accounts := s.vs_accounts;
       cr_tStorage := s.vs_transient |>
End

(* retOff/retSize are natural offsets/sizes, just as in the existing writer.
 * Only TAKE retSize actual bytes are written: no zero-padding to retSize.
 * This is deliberately not an exec_result evaluator or a second dispatch.
 *)
Definition consume_call_outcome_def:
  consume_call_outcome rq retOff retSize s =
    let (outcome, rest) = take_outcome rq s.vs_outcomes;
        (accounts, ts, logs) = adopt_outcome rq outcome
          (s.vs_accounts, s.vs_transient, s.vs_logs);
        result : bytes32 = if outcome.co_success then 1w else 0w
    in (result, s with <|
         vs_outcomes := rest;
         vs_requests := record_request rq s.vs_requests;
         vs_accounts := accounts;
         vs_transient := ts;
         vs_logs := logs;
         vs_returndata := outcome.co_returnData;
         vs_memory := (write_memory_with_expansion retOff
           (TAKE retSize outcome.co_returnData) s).vs_memory |>)
End
