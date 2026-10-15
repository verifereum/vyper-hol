(* Retained CLOSED TASK040 pre-activation counterexamples and focused probes.
 * These exercise the future shared completion helper, NOT current CALL.
 * Existing primitive-preservation exports remain true on current semantics;
 * they cannot be reused unchanged after the dispatcher consumes outcomes.
 *)
Theory venomCallOracleRegression
Ancestors
  venomCallOracleDefs venomCallOracleProps venomState venomInst
  venomExecSemantics extCallOracle stateFrame vfmState vfmTypes
  arithmetic list pair words
Libs
  wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

Definition call_probe_state_def:
  call_probe_state = init_venom_state "entry" with
    vs_memory := [1w; 2w; 3w; 4w]
End

Definition call_probe_request_def:
  call_probe_request = venom_call_request call_probe_state 8w 0w 0w 1w F
End

Definition call_probe_outcome_def:
  call_probe_outcome =
    <| co_success := T;
       co_returnData := [9w];
       co_accounts := ((8w:address) =+
         (empty_account_state with balance := 23)) empty_accounts;
       co_tStorage := K (K (42w:bytes32));
       co_logs := [<| logger := 8w; topics := [1w]; data := [42w] |>] |>
End

(* Simplify the projections before EVAL: evaluating an entire function-valued
 * state record obscures the small closed arithmetic/list checks here. *)
val probe_defs =
  [call_probe_state_def, call_probe_request_def, call_probe_outcome_def,
   init_venom_state_def, empty_call_context_def, venom_call_request_def,
   read_memory_def, consume_call_outcome_def, take_outcome_def,
   computed_precompile_addresses, record_request_def, failed_outcome_def,
   adopt_outcome_def, write_memory_with_expansion_def,
   update_var_def, lookup_var_def, mk_inst_def, step_inst_base_def,
   w2w_n2w];

(* A failed outcome is still consumed and the ordinary request still recorded.
 * This closed witness invalidates BOTH single-state preservation projections
 * once this helper is wired into CALL or STATICCALL.
 *)
Theorem outcome_consumption_not_preservation:
  let s = call_probe_state with vs_outcomes := [failed_outcome call_probe_request];
      t = SND (consume_call_outcome call_probe_request 1 3 s)
  in t.vs_outcomes <> s.vs_outcomes /\ t.vs_requests <> s.vs_requests
Proof
  simp probe_defs >> EVAL_TAC
QED

(* Even identical initial full records do not suffice for arbitrary paired
 * instructions: an outcome-consuming call versus actual NOP diverges.
 * This is the counterexample pattern for the new arbitrary-i1/i2 exports
 * in 036/037/038/039, not a claim that current step_inst_base is false.
 *)
Theorem outcome_consumption_vs_nop:
  let s = call_probe_state with vs_outcomes := [failed_outcome call_probe_request];
      t = SND (consume_call_outcome call_probe_request 1 3 s)
  in step_inst_base (mk_inst 0 NOP [] []) s = OK s /\
     execution_frame s = execution_frame s /\
     t.vs_outcomes <> s.vs_outcomes /\ t.vs_requests <> s.vs_requests
Proof
  simp probe_defs >> EVAL_TAC
QED

(* Pairing two calls does not repair the false arbitrary-instruction claim:
 * unequal actual targets yield unequal requests despite equal initial state.
 *)
Theorem unequal_targets_not_transport:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
      rq1 = venom_call_request s 8w 0w 0w 1w F;
      rq2 = venom_call_request s 9w 0w 0w 1w F;
      t1 = SND (consume_call_outcome rq1 1 3 s);
      t2 = SND (consume_call_outcome rq2 1 3 s)
  in t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests <> t2.vs_requests
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_ordinary_success_short_write:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
      (word, t) = consume_call_outcome call_probe_request 1 3 s
  in word = 1w /\ t.vs_outcomes = [] /\
     t.vs_requests = [call_probe_request] /\ t.vs_returndata = [9w] /\
     t.vs_memory = [1w; 9w; 3w; 4w] /\
     t.vs_accounts = call_probe_outcome.co_accounts /\
     t.vs_transient = call_probe_outcome.co_tStorage /\
     t.vs_logs = call_probe_outcome.co_logs /\
     lookup_var "result" (update_var "result" word t) = SOME 1w
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_failed_short_write:
  let s = call_probe_state with vs_outcomes :=
            [call_probe_outcome with co_success := F];
      (word, t) = consume_call_outcome call_probe_request 1 3 s
  in word = 0w /\ t.vs_outcomes = [] /\
     t.vs_requests = [call_probe_request] /\ t.vs_returndata = [9w] /\
     t.vs_memory = [1w; 9w; 3w; 4w] /\
     t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
     t.vs_logs = s.vs_logs /\
     lookup_var "result" (update_var "result" word t) = SOME 0w
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_exhausted:
  let (word, t) = consume_call_outcome call_probe_request 1 3 call_probe_state
  in word = 0w /\ t.vs_outcomes = [] /\
     t.vs_requests = [call_probe_request] /\ t.vs_returndata = [] /\
     t.vs_memory = call_probe_state.vs_memory /\
     t.vs_accounts = call_probe_state.vs_accounts /\
     t.vs_transient = call_probe_state.vs_transient /\
     t.vs_logs = call_probe_state.vs_logs
Proof
  simp probe_defs >> EVAL_TAC
QED

(* Staticness is inherited even for CALL's is_static = F. Success and
 * nonempty returndata do not imply adoption of a malicious static outcome.
 *)
Theorem consume_inherited_static:
  let s = call_probe_state with <|
        vs_outcomes := [call_probe_outcome];
        vs_call_ctx := empty_call_context with cc_static := T |>;
      rq = venom_call_request s 8w 0w 0w 1w F;
      (word, t) = consume_call_outcome rq 1 3 s
  in rq.cr_static /\ word = 1w /\ t.vs_outcomes = [] /\
     t.vs_requests = [rq] /\ t.vs_returndata = [9w] /\
     t.vs_memory = [1w; 9w; 3w; 4w] /\
     t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
     t.vs_logs = s.vs_logs
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_explicit_static:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
      rq = venom_call_request s 8w 0w 0w 1w T;
      (word, t) = consume_call_outcome rq 1 3 s
  in rq.cr_static /\ word = 1w /\ t.vs_outcomes = [] /\
     t.vs_requests = [rq] /\ t.vs_accounts = s.vs_accounts /\
     t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_short_write_expansion:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
      t = SND (consume_call_outcome call_probe_request 5 3 s)
  in t.vs_memory = [1w; 2w; 3w; 4w; 0w; 9w] /\ LENGTH t.vs_memory = 6
Proof
  simp probe_defs >> EVAL_TAC
QED

Theorem consume_zero_size_write:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
      t = SND (consume_call_outcome call_probe_request 1 0 s)
  in t.vs_memory = s.vs_memory /\ t.vs_returndata = [9w]
Proof
  simp probe_defs >> EVAL_TAC
QED

(* The precompile contracts are already kernel-proved in extCallOracle.
 * These probes check the actual Venom completion, using arbitrary nonempty
 * oracle/trace payloads: computed calls consume/record neither one.
 *)
Theorem consume_computed_ecrecover:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
                                  vs_requests := [call_probe_request] |>;
      rq = venom_call_request s 1w 0w 0w 0w F;
      (word, t) = consume_call_outcome rq 1 3 s
  in word = 1w /\ t.vs_outcomes = s.vs_outcomes /\
     t.vs_requests = s.vs_requests /\ t.vs_returndata = [] /\
     t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
     t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs
Proof
  simp[venom_call_request_def, read_memory_def, consume_call_outcome_def,
       take_outcome_def, record_request_def, computed_precompile_def,
       precompile_result_empty_ecrecover, failed_outcome_def,
       adopt_outcome_def, write_memory_with_expansion_def,
       call_probe_state_def, init_venom_state_def, empty_call_context_def,
       w2w_n2w]
QED

Theorem consume_computed_sha256:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
                                  vs_requests := [call_probe_request] |>;
      rq = venom_call_request s 2w 0w 0w 0w F;
      (word, t) = consume_call_outcome rq 1 0 s
  in word = 1w /\ t.vs_outcomes = s.vs_outcomes /\
     t.vs_requests = s.vs_requests /\ LENGTH t.vs_returndata = 32 /\
     t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
     t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs
Proof
  simp[venom_call_request_def, read_memory_def, consume_call_outcome_def,
       take_outcome_def, record_request_def, computed_precompile_def,
       failed_outcome_def, adopt_outcome_def, write_memory_with_expansion_def,
       call_probe_state_def, init_venom_state_def, empty_call_context_def,
       byteTheory.LENGTH_word_to_bytes, w2w_n2w]
QED

Theorem consume_computed_empty_ec:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
                                  vs_requests := [call_probe_request] |>;
      rq6 = venom_call_request s 6w 0w 0w 0w F;
      rq7 = venom_call_request s 7w 0w 0w 0w F
  in consume_call_outcome rq6 1 0 s =
       (1w, s with vs_returndata := REPLICATE 64 0w) /\
     consume_call_outcome rq7 1 0 s =
       (1w, s with vs_returndata := REPLICATE 64 0w)
Proof
  simp[venom_call_request_def, read_memory_def, consume_call_outcome_def,
       take_outcome_def, record_request_def, computed_precompile_def,
       precompile_result_empty_ec, failed_outcome_def, adopt_outcome_def,
       write_memory_with_expansion_def, call_probe_state_def,
       init_venom_state_def, empty_call_context_def, w2w_n2w]
QED

Theorem consume_computed_invalid_ec:
  let s = call_probe_state with <|
        vs_memory := REPLICATE 63 0w ++ [1w];
        vs_outcomes := [call_probe_outcome];
        vs_requests := [call_probe_request] |>;
      rq6 = venom_call_request s 6w 0w 0w 64w F;
      rq7 = venom_call_request s 7w 0w 0w 64w F
  in consume_call_outcome rq6 1 3 s = (0w, s with vs_returndata := []) /\
     consume_call_outcome rq7 1 3 s = (0w, s with vs_returndata := [])
Proof
  simp[venom_call_request_def, read_memory_def, consume_call_outcome_def,
       take_outcome_def, record_request_def, computed_precompile_def,
       precompile_result_invalid_ec, failed_outcome_def, adopt_outcome_def,
       write_memory_with_expansion_def, call_probe_state_def,
       init_venom_state_def, empty_call_context_def, w2w_n2w,
       TAKE_APPEND1, TAKE_APPEND2] >> EVAL_TAC
QED

(* Nonzero value to a precompile is an ordinary oracle call. Also exercise
 * a retained nonempty oracle suffix and appending to an existing trace. *)
Theorem consume_nonzero_precompile_ordinary:
  let s = call_probe_state with <|
        vs_outcomes := [call_probe_outcome; failed_outcome call_probe_request];
        vs_requests := [call_probe_request] |>;
      rq = venom_call_request s 2w 1w 0w 1w F;
      (word, t) = consume_call_outcome rq 1 3 s
  in word = 1w /\
     t.vs_outcomes = [failed_outcome call_probe_request] /\
     t.vs_requests = [call_probe_request; rq] /\ t.vs_returndata = [9w] /\
     t.vs_memory = [1w; 9w; 3w; 4w]
Proof
  simp probe_defs >> EVAL_TAC
QED
