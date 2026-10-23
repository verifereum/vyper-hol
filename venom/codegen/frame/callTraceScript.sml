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
  arithmetic list option pair sum relation finite_map words byte
  extCallOracle vfmTypes vfmState vfmContext vfmExecution
  vfmExecutionProp vfmDecreasesGas
Libs
  BasicProvers

(* ===== Observer state and extraction ===== *)

Datatype:
  trace_obs = <| entries : (call_request # call_outcome) list;
                 readings : bytes32 list;
                 pending : (call_request # num) option |>
End

(* pending stores our request and our pre-call log count, not a callee's
 * log count. Descendant calls must not overwrite it. *)
Definition next_opcode_def:
  next_opcode c =
    if LENGTH c.msgParams.code <= c.pc then SOME Stop
    else FLOOKUP c.msgParams.parsed c.pc
End

Definition observable_call_def:
  observable_call c <=>
    (next_opcode c = SOME Call /\ 7 <= LENGTH c.stack) \/
    (next_opcode c = SOME StaticCall /\ 6 <= LENGTH c.stack) \/
    (next_opcode c = SOME Create /\ 3 <= LENGTH c.stack) \/
    (next_opcode c = SOME Create2 /\ 4 <= LENGTH c.stack)
End

(* Called only under observable_call by observe. The total extractor uses
 * top-first stack order; the gas and output-buffer operands are omitted.
 * Accounts are live rollback accounts, NOT the saved frame snapshot. *)
Definition request_of_def:
  request_of s =
    let c = FST (HD s.contexts);
        valueOffset = if next_opcode c = SOME Call then 1 else 0
    in if next_opcode c = SOME Create \/ next_opcode c = SOME Create2 then
         <| cr_kind := if next_opcode c = SOME Create2 then
                         Create2Call (EL 3 c.stack) else CreateCall;
            cr_gas := NONE;
            cr_data_len := w2n (EL 2 c.stack);
            cr_target := 0w;
            cr_value := w2n (HD c.stack);
            cr_data := take_pad_0 (w2n (EL 2 c.stack))
                         (DROP (w2n (EL 1 c.stack)) c.memory);
            cr_static := F;
            cr_accounts := s.rollback.accounts;
            cr_tStorage := s.rollback.tStorage |>
       else <| cr_kind := MessageCall; cr_gas := NONE;
          cr_data_len := w2n (EL (3 + valueOffset) c.stack);
          cr_target := w2w (EL 1 c.stack);
          cr_value := if valueOffset = 1 then w2n (EL 2 c.stack) else 0;
          cr_data := take_pad_0 (w2n (EL (3 + valueOffset) c.stack))
                       (DROP (w2n (EL (2 + valueOffset) c.stack)) c.memory);
          cr_static := (next_opcode c = SOME StaticCall \/ c.msgParams.static);
          cr_accounts := s.rollback.accounts;
          cr_tStorage := s.rollback.tStorage |>
End

(* The caller's post-step top stack word is the success flag. Only logs
 * after the saved pre-call count belong to this outcome. *)
Definition outcome_of_def:
  outcome_of kind s n =
    let c = FST (HD s.contexts)
    in <| co_created := if kind = MessageCall then 0w else w2w (HD c.stack);
          co_toDelete := s.rollback.toDelete;
          co_success := (HD c.stack <> 0w);
          co_returnData := c.returnData;
          co_accounts := s.rollback.accounts;
          co_tStorage := s.rollback.tStorage;
          co_logs := DROP n c.logs |>
End

(* ===== Exact observer table (PLAN section 5.2) ===== *)

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
                 [(request_of s, outcome_of (request_of s).cr_kind s' (LENGTH c.logs))]
             else if LENGTH s'.contexts = d + 1 then
               obs with pending := SOME (request_of s, LENGTH c.logs)
             else obs
           else obs
         else if LENGTH s.contexts > d /\ LENGTH s'.contexts = d then
           case obs.pending of
             NONE => obs
           | SOME (rq, n) => obs with
               <| entries := obs.entries ++ [(rq, outcome_of rq.cr_kind s' n)];
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

(* CREATE operands are value, offset, size, and (for CREATE2) salt, top first.
   Zero padding is shared with the EVM memory reader. *)
Theorem request_of_create:
  next_opcode (FST (HD s.contexts)) = SOME Create ==>
  request_of s =
    <| cr_kind := CreateCall; cr_gas := NONE;
       cr_data_len := w2n (EL 2 (FST (HD s.contexts)).stack);
       cr_target := 0w;
       cr_value := w2n (HD (FST (HD s.contexts)).stack);
       cr_data := take_pad_0 (w2n (EL 2 (FST (HD s.contexts)).stack))
         (DROP (w2n (EL 1 (FST (HD s.contexts)).stack))
           (FST (HD s.contexts)).memory);
       cr_static := F; cr_accounts := s.rollback.accounts;
       cr_tStorage := s.rollback.tStorage |>
Proof
  simp[request_of_def]
QED

Theorem request_of_create2:
  next_opcode (FST (HD s.contexts)) = SOME Create2 ==>
  (request_of s).cr_kind = Create2Call (EL 3 (FST (HD s.contexts)).stack) /\
  (request_of s).cr_target = 0w /\
  (request_of s).cr_value = w2n (HD (FST (HD s.contexts)).stack) /\
  (request_of s).cr_data_len = w2n (EL 2 (FST (HD s.contexts)).stack) /\
  (request_of s).cr_data =
    take_pad_0 (w2n (EL 2 (FST (HD s.contexts)).stack))
      (DROP (w2n (EL 1 (FST (HD s.contexts)).stack))
        (FST (HD s.contexts)).memory) /\
  ~(request_of s).cr_static /\ (request_of s).cr_gas = NONE
Proof
  simp[request_of_def]
QED

Theorem create_request_not_computed:
  (next_opcode (FST (HD s.contexts)) = SOME Create \/
   next_opcode (FST (HD s.contexts)) = SOME Create2) ==>
  ~computed_precompile (request_of s)
Proof
  strip_tac >> simp[request_of_def, computed_precompile_def]
QED

Theorem observable_create_stack:
  (next_opcode c = SOME Create ==> (observable_call c <=> 3 <= LENGTH c.stack)) /\
  (next_opcode c = SOME Create2 ==> (observable_call c <=> 4 <= LENGTH c.stack))
Proof
  simp[observable_call_def]
QED

(* The request kind is retained across entry/return: the post-step pc no
   longer identifies the creating opcode. Failed outcomes keep live accounts
   (including the nonce increment); adoption filters logs/deletions separately. *)
Theorem outcome_of_fields:
  (outcome_of kind s n).co_accounts = s.rollback.accounts /\
  (outcome_of kind s n).co_tStorage = s.rollback.tStorage /\
  (outcome_of kind s n).co_toDelete = s.rollback.toDelete /\
  (outcome_of kind s n).co_logs = DROP n (FST (HD s.contexts)).logs /\
  (outcome_of kind s n).co_returnData = (FST (HD s.contexts)).returnData /\
  ((outcome_of kind s n).co_success <=> HD (FST (HD s.contexts)).stack <> 0w) /\
  (outcome_of kind s n).co_created =
    (if kind = MessageCall then 0w else w2w (HD (FST (HD s.contexts)).stack))
Proof
  simp[outcome_of_def]
QED

Theorem observe_same_depth_create:
  LENGTH s.contexts = d /\ LENGTH post.contexts = d /\
  ((next_opcode (FST (HD s.contexts)) = SOME Create /\
      3 <= LENGTH (FST (HD s.contexts)).stack) \/
   (next_opcode (FST (HD s.contexts)) = SOME Create2 /\
      4 <= LENGTH (FST (HD s.contexts)).stack)) ==>
  observe d s (INL (), post) obs =
    obs with entries := obs.entries ++
      [(request_of s, outcome_of (request_of s).cr_kind post
         (LENGTH (FST (HD s.contexts)).logs))]
Proof
  strip_tac >> simp[observe_def, observable_call_def]
QED

Theorem observe_enter_create:
  LENGTH s.contexts = d /\ LENGTH post.contexts = d + 1 /\
  ((next_opcode (FST (HD s.contexts)) = SOME Create /\
      3 <= LENGTH (FST (HD s.contexts)).stack) \/
   (next_opcode (FST (HD s.contexts)) = SOME Create2 /\
      4 <= LENGTH (FST (HD s.contexts)).stack)) ==>
  observe d s (INL (), post) obs =
    obs with pending := SOME (request_of s, LENGTH (FST (HD s.contexts)).logs)
Proof
  strip_tac >> simp[observe_def, observable_call_def]
QED

Theorem observe_return_pending:
  d < LENGTH s.contexts /\ LENGTH post.contexts = d /\
  obs.pending = SOME (rq, n) ==>
  observe d s (INL (), post) obs =
    obs with <| entries := obs.entries ++ [(rq, outcome_of rq.cr_kind post n)];
                pending := NONE |>
Proof
  rpt strip_tac >> simp[observe_def]
QED

Theorem create_trace_same_depth:
  step es = (INL (), post) /\ step post = (INR exc, last) /\
  LENGTH es.contexts = LENGTH post.contexts /\
  ((next_opcode (FST (HD es.contexts)) = SOME Create /\
      3 <= LENGTH (FST (HD es.contexts)).stack) \/
   (next_opcode (FST (HD es.contexts)) = SOME Create2 /\
      4 <= LENGTH (FST (HD es.contexts)).stack)) ==>
  call_trace es = [(request_of es,
    outcome_of (request_of es).cr_kind post (LENGTH (FST (HD es.contexts)).logs))]
Proof
  strip_tac >>
  simp[call_trace_def, full_call_trace_def, frame_obs_def] >>
  simp[Once frame_obs_tr_def, observe_def, observable_call_def] >>
  simp[Once frame_obs_tr_def, observe_def, create_request_not_computed]
QED

Theorem create_trace_enter_return:
  step es = (INL (), child) /\ step child = (INL (), post) /\
  step post = (INR exc, last) /\
  LENGTH child.contexts = LENGTH es.contexts + 1 /\
  LENGTH post.contexts = LENGTH es.contexts /\
  ((next_opcode (FST (HD es.contexts)) = SOME Create /\
      3 <= LENGTH (FST (HD es.contexts)).stack) \/
   (next_opcode (FST (HD es.contexts)) = SOME Create2 /\
      4 <= LENGTH (FST (HD es.contexts)).stack)) ==>
  call_trace es = [(request_of es,
    outcome_of (request_of es).cr_kind post (LENGTH (FST (HD es.contexts)).logs))]
Proof
  strip_tac >>
  simp[call_trace_def, full_call_trace_def, frame_obs_def] >>
  simp[Once frame_obs_tr_def, observe_def, observable_call_def] >>
  simp[Once frame_obs_tr_def, observe_def] >>
  simp[Once frame_obs_tr_def, observe_def, create_request_not_computed]
QED

(* Nonzero offset and a short backing memory distinguish padding from TAKE,
   and distinguish the value/offset/size slots from the CALL layout. *)
Theorem trace_dimindex_256[local]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem create2_request_padding_probe:
  next_opcode (FST (HD s.contexts)) = SOME Create2 /\
  (FST (HD s.contexts)).stack = [7w; 1w; 3w; 42w] /\
  (FST (HD s.contexts)).memory = [9w; 8w] ==>
  observable_call (FST (HD s.contexts)) /\
  (request_of s).cr_kind = Create2Call 42w /\
  (request_of s).cr_value = 7 /\
  (request_of s).cr_data = [8w; 0w; 0w] /\
  (request_of s).cr_data_len = 3
Proof
  simp[observable_call_def, request_of_def, take_pad_0_def,
       dimword_def, trace_dimindex_256] >> EVAL_TAC
QED

Theorem create_outcome_zero_probe:
  HD (FST (HD s.contexts)).stack = 0w ==>
  ~(outcome_of CreateCall s n).co_success /\
  (outcome_of CreateCall s n).co_created = 0w /\
  (outcome_of CreateCall s n).co_accounts = s.rollback.accounts
Proof
  simp[outcome_of_def, w2w_def]
QED

Theorem create_outcome_address_probe:
  HD (FST (HD s.contexts)).stack = 42w ==>
  (outcome_of (Create2Call salt) s n).co_success /\
  (outcome_of (Create2Call salt) s n).co_created = 42w /\
  (outcome_of MessageCall s n).co_created = 0w
Proof
  simp[outcome_of_def, w2w_def, dimword_def, trace_dimindex_256] >> EVAL_TAC
QED

val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("callTrace oracle dependency: " ^ name))
  (DB.thms "callTrace");
