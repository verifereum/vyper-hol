(* Request/completion plumbing for the external-call outcome oracle (PLAN 5.4).
 * Used by exec_ext_call (venomExecSemantics) for CALL and STATICCALL.
 * TOP-LEVEL: venom_call_request (already-evaluated operands),
 * consume_call_outcome (success word and state, before output binding).
 * Gas evaluation and single-output validation remain the dispatcher's job.
 *)
Theory venomCallOracleDefs
Ancestors
  venomState extCallOracle pair

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
        (accounts, ts, logs, pending) = adopt_outcome rq outcome
          (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_pending_deletions);
        result : bytes32 = if outcome.co_success then 1w else 0w
    in (result, s with <|
         vs_outcomes := rest;
         vs_requests := record_request rq s.vs_requests;
         vs_accounts := accounts;
         vs_transient := ts;
         vs_logs := logs;
          vs_pending_deletions := pending;
         vs_returndata := outcome.co_returnData;
         vs_memory := (write_memory_with_expansion retOff
           (TAKE retSize outcome.co_returnData) s).vs_memory |>)
End

(* Eliminate tuple case plumbing once for activated dispatch consumers.
 * Unchanged-field projections then simplify without per-field APIs. *)
Theorem consume_call_outcome_eq[simp]:
  consume_call_outcome rq ro rs s =
    (if (FST (take_outcome rq s.vs_outcomes)).co_success then 1w else 0w,
     s with <|
       vs_outcomes := SND (take_outcome rq s.vs_outcomes);
       vs_requests := record_request rq s.vs_requests;
       vs_accounts := FST (adopt_outcome rq
         (FST (take_outcome rq s.vs_outcomes))
          (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_pending_deletions));
       vs_transient := FST (SND (adopt_outcome rq
         (FST (take_outcome rq s.vs_outcomes))
          (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_pending_deletions)));
        vs_logs := FST (SND (SND (adopt_outcome rq
         (FST (take_outcome rq s.vs_outcomes))
          (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_pending_deletions))));
        vs_pending_deletions := SND (SND (SND (adopt_outcome rq
          (FST (take_outcome rq s.vs_outcomes))
          (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_pending_deletions))));
       vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData;
       vs_memory := (write_memory_with_expansion ro
         (TAKE rs (FST (take_outcome rq s.vs_outcomes)).co_returnData) s).vs_memory |>)
Proof
  simp[consume_call_outcome_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED

(* No output buffer size can change a completion with empty returndata. *)
Theorem consume_call_outcome_empty_output_size:
  !rq ro rs s w t rs'.
    consume_call_outcome rq ro rs s = (w,t) /\ t.vs_returndata = [] ==>
    consume_call_outcome rq ro rs' s = (w,t)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[consume_call_outcome_def, Excl "consume_call_outcome_eq"] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[]
QED
