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
    <| cr_kind := MessageCall; cr_gas := NONE;
       cr_data_len := LENGTH (read_memory (w2n argsOff) (w2n argsSize) s);
       cr_target := w2w addr;
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
         vs_toDelete := if computed_precompile rq then s.vs_toDelete
                       else adopt_outcome_deletions rq outcome s.vs_toDelete;
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
         (s.vs_accounts, s.vs_transient, s.vs_logs));
       vs_transient := FST (SND (adopt_outcome rq
         (FST (take_outcome rq s.vs_outcomes))
         (s.vs_accounts, s.vs_transient, s.vs_logs)));
       vs_logs := SND (SND (adopt_outcome rq
         (FST (take_outcome rq s.vs_outcomes))
         (s.vs_accounts, s.vs_transient, s.vs_logs)));
       vs_toDelete := if computed_precompile rq then s.vs_toDelete
         else adopt_outcome_deletions rq
           (FST (take_outcome rq s.vs_outcomes)) s.vs_toDelete;
       vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData;
       vs_memory := (write_memory_with_expansion ro
         (TAKE rs (FST (take_outcome rq s.vs_outcomes)).co_returnData) s).vs_memory |>)
Proof
  simp[consume_call_outcome_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED

(* CREATE has no return-memory buffer.  Its input is a private initcode
 * snapshot and its result is the oracle's address, not a success flag. *)
Definition venom_create_request_def:
  venom_create_request s (value:bytes32) (offset:bytes32) (sz:bytes32) salt_opt =
    <| cr_kind := (case salt_opt of NONE => CreateCall | SOME salt => Create2Call salt);
       cr_gas := NONE;
       cr_data_len := LENGTH (read_memory (w2n offset) (w2n sz) s);
       cr_target := 0w; cr_value := w2n value;
       cr_data := read_memory (w2n offset) (w2n sz) s;
       cr_static := F; cr_accounts := s.vs_accounts;
       cr_tStorage := s.vs_transient |>
End

Definition consume_create_outcome_def:
  consume_create_outcome rq s =
    let (outcome, rest) = take_outcome rq s.vs_outcomes;
        (accounts, ts, logs) = adopt_outcome rq outcome
          (s.vs_accounts, s.vs_transient, s.vs_logs);
        result : bytes32 = if outcome.co_success then w2w outcome.co_created else 0w
    in (result, s with <|
         vs_outcomes := rest;
         vs_requests := record_request rq s.vs_requests;
         vs_accounts := accounts; vs_transient := ts; vs_logs := logs;
         vs_toDelete := adopt_outcome_deletions rq outcome s.vs_toDelete;
         vs_returndata := outcome.co_returnData |>)
End

Theorem consume_create_outcome_eq[simp]:
  consume_create_outcome rq s =
    (if (FST (take_outcome rq s.vs_outcomes)).co_success
     then w2w (FST (take_outcome rq s.vs_outcomes)).co_created else 0w,
     s with <|
       vs_outcomes := SND (take_outcome rq s.vs_outcomes);
       vs_requests := record_request rq s.vs_requests;
       vs_accounts := FST (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
         (s.vs_accounts, s.vs_transient, s.vs_logs));
       vs_transient := FST (SND (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
         (s.vs_accounts, s.vs_transient, s.vs_logs)));
       vs_logs := SND (SND (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
         (s.vs_accounts, s.vs_transient, s.vs_logs)));
       vs_toDelete := adopt_outcome_deletions rq
         (FST (take_outcome rq s.vs_outcomes)) s.vs_toDelete;
       vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData |>)
Proof
  simp[consume_create_outcome_def] >> pairarg_tac >> simp[] >>
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
