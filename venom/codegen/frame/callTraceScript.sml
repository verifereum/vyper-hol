(* Frame-local observers for the run_call execution boundary.
 * TOP-LEVEL: trace_obs, next_opcode, request_of, outcome_of, observe,
 * frame_obs_tr, frame_obs, full_call_trace, call_trace, gas_readings,
 * precompile_call_starved.
 * Helper: observable_call (the Call/StaticCall stack-shape guard).
 * Totality uses only Verifereum's step gas-decrease theorem; semantic
 * trace/observer correctness is deliberately deferred to Milestone 2.1.
 *)
Theory callTrace
Ancestors
  arithmetic list rich_list option pair sum relation finite_map words byte
  extCallOracle vfmTypes vfmState vfmContext vfmExecution
  vfmExecutionProp vfmDecreasesGas
Libs
  BasicProvers

(* ===== Observer state and extraction ===== *)

Datatype:
  trace_obs = <| entries : (call_request # call_outcome) list;
                 readings : bytes32 list;
                 pending : (call_request # num # num) option |>
End

(* Save the caller's log and deletion counts. Descendants must not overwrite
 * this frame's pending request. Deletions grow by consing, unlike logs. *)
Definition next_opcode_def:
  next_opcode c =
    if LENGTH c.msgParams.code <= c.pc then SOME Stop
    else FLOOKUP c.msgParams.parsed c.pc
End

Definition observable_call_def:
  observable_call c <=>
    (next_opcode c = SOME Call /\ 7 <= LENGTH c.stack) \/
    (next_opcode c = SOME StaticCall /\ 6 <= LENGTH c.stack)
End

(* Called only under observable_call by observe. The total extractor uses
 * top-first stack order; the gas and output-buffer operands are omitted.
 * Accounts are live rollback accounts, NOT the saved frame snapshot. *)
Definition request_of_def:
  request_of s =
    let c = FST (HD s.contexts);
        valueOffset = if next_opcode c = SOME Call then 1 else 0
    in <| cr_target := w2w (EL 1 c.stack);
          cr_value := if valueOffset = 1 then w2n (EL 2 c.stack) else 0;
          cr_data := take_pad_0 (w2n (EL (3 + valueOffset) c.stack))
                       (DROP (w2n (EL (2 + valueOffset) c.stack))
                         (buffer_to_list c.memory));
          cr_static := (next_opcode c = SOME StaticCall \/ c.msgParams.static);
          cr_accounts := s.rollback.accounts;
          cr_tStorage := s.rollback.tStorage |>
End

(* The caller's post-step top stack word is the success flag. Only logs
 * after the saved pre-call count belong to this outcome. *)
Definition outcome_of_def:
  outcome_of s n m =
    let c = FST (HD s.contexts)
    in <| co_success := (HD c.stack <> 0w);
          co_returnData := c.returnData;
          co_accounts := s.rollback.accounts;
          co_tStorage := s.rollback.tStorage;
          co_logs := DROP n c.logs;
          co_toDelete :=
            TAKE (LENGTH s.rollback.toDelete - m) s.rollback.toDelete |>
End

(* ===== Exact observer table (PLAN section 5.2) ===== *)

Theorem outcome_of_added_deletions:
  s.rollback.toDelete = added ++ previous ==>
  (outcome_of s log_count (LENGTH previous)).co_toDelete = added
Proof
  simp[outcome_of_def, TAKE_LENGTH_APPEND]
QED

Definition observe_def:
  observe d s (r, s') obs =
    if ISL r then
      let c = FST (HD s.contexts);
          c' = FST (HD s'.contexts)
      in if LENGTH s.contexts = d then
           if next_opcode c = SOME Gas /\ LENGTH s'.contexts = d then
             obs with readings := obs.readings ++ [HD c'.stack]
           else if observable_call c then
             if LENGTH s'.contexts = d then
               obs with entries := obs.entries ++
                 [(request_of s, outcome_of s' (LENGTH c.logs)
                    (LENGTH s.rollback.toDelete))]
             else if LENGTH s'.contexts = d + 1 then
               obs with pending := SOME
                 (request_of s, LENGTH c.logs, LENGTH s.rollback.toDelete)
             else obs
           else obs
         else if LENGTH s.contexts > d /\ LENGTH s'.contexts = d then
           case obs.pending of
             NONE => obs
           | SOME (rq, n, m) => obs with
               <| entries := obs.entries ++ [(rq, outcome_of s' n m)];
                  pending := NONE |>
         else obs
    else obs
End

(* ===== Total run_call-shaped traversal ===== *)

(* The measure projects onto d and the POST-step (r,s') exactly as in
 * run_call_tr. Neither the pre-step state nor the observer affects it. *)
Definition frame_obs_tr_def:
  frame_obs_tr d obs s (r, s') =
    let obs' = observe d s (r, s') obs in
    if ISR r \/ LENGTH s'.contexts < d then obs'
    else frame_obs_tr d obs' s' (step s')
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<))
    (\(d, obs, s, (r, s')).
      if ISR r \/ LENGTH s'.contexts < d then ((0:num), (0, 0))
      else (1, contexts_weight 0 s'.contexts))` >>
  rpt gen_tac >>
  rename1 `step post` >>
  mp_tac (Q.SPEC `post` (REWRITE_RULE [decreases_gas_cred_def]
    decreases_gas_cred_step)) >>
  IF_CASES_TAC >- (
    rw[contexts_weight_def, unused_gas_def] >>
    gvs[step_def, handle_def, get_current_context_def, bind_def, fail_def] >>
    gvs[handle_step_def, reraise_def]) >>
  rw[] >> fs[LEX_DEF, UNCURRY] >>
  metis_tac[sum_CASES, ISL, ISR]
End

Definition frame_obs_def:
  frame_obs es =
    frame_obs_tr (LENGTH es.contexts)
      <| entries := []; readings := []; pending := NONE |> es (step es)
End

Definition full_call_trace_def:
  full_call_trace es = (frame_obs es).entries
End

(* Keep every other call, including nonzero-value calls to these addresses
 * and precompiles outside the computed set 1/2/6/7. *)
Definition call_trace_def:
  call_trace es =
    FILTER (\(rq, outcome). ~computed_precompile rq) (full_call_trace es)
End

Definition gas_readings_def:
  gas_readings es = (frame_obs es).readings
End

(* Valid computed input with a failed EVM outcome: insufficient forwarded
 * gas or call-depth failure. Invalid ecadd/ecmul input is NOT starvation.
 * Invalid ecrecover is valid here: its specified success output is []. *)
Definition precompile_call_starved_def:
  precompile_call_starved es <=>
    ?rq outcome bs.
      MEM (rq, outcome) (full_call_trace es) /\ rq.cr_value = 0 /\
      precompile_result rq.cr_target rq.cr_data = SOME (SOME bs) /\
      ~outcome.co_success
End
