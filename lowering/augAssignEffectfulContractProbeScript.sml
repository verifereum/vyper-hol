(* Replay boundary: success at one observation list is not sufficient. *)
Theory augAssignEffectfulContractProbe
Ancestors
  gasExemptCert vyperState

Theorem source_replay_excludes_gas_exempt_cert:
  (!obs err ee.
     source (es with gas_obs := obs) = (INR (Error err), ee) ==>
     ~unspecified_behaviour_exempt tops err) ==>
  ~gas_exempt_cert memory tops (ctx,func) source (es,s0)
     marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >> strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  metis_tac[]
QED

(* Contract audit C1.4.3.3: target admission has an existing theorem route;
   concrete full-program admission and replay remain uninstantiated.

   Universal target admission table (all cited results are existing
   TASK-authorized admissions, not new facts proved by this file):
   - targetPlaceSimCases.target_case_all requires target_idx_case.
   - target_idx_case_ok requires int_calls_target bt = [] and expr_ok
     for every member of target_indices bt. The proposed root is a global,
     indices are literal zero and an external call with literal target
     and no arguments/kwargs. Neither contains an internal call, so this
     is a syntactic empty-int-calls obligation, not a storage condition.
   - exprSimMain.compile_expr_sim_mutual's first conjunct supplies
     !cenv e. expr_ok cenv e, including both index expressions. Its
     ancestors are expression theories, not bodyAugAssignOther; using
     this already admitted interface does not require body correctness.
   - Alternatively compile_extcall_case provides BOTH expr_sim_case and
     expr_vv_case from exprs_case for TAKE 1 args, results_case for the
     positional slice, and exprs_case for kwargs; literal target and empty
     slices are the only cases in the proposed no-arguments call.
     exprSimHyps.expr_case_of_ok supplies both cases for a call-free
     literal. This avoids assuming one-state target_post implies a case.
   - target_case quantifies over all env/es meeting target_pre. These
     admitted theorems discharge that universal judgment directly;
     concrete target_indices_pre (static typing and byte/alloc/call-safe
     checks) and initial expr_sim_inv STILL require program instantiation.
   None of these target-case prerequisites asserts raw canonicality of
   a dead selected scalar. The storage place_readable clause is T and
   place_ptr_rel identifies slot/type, not the selected payload word.

   Source replay audit:
   - Plain ExtCall with literal address, no positional args, no kwargs,
     no defaults, and SOME outcomes does NOT call next_gas_reading.
     eval_ext_call forwards a constant default gas; eval_ext_call_effects
     selects the oracle branch, and take/adopt_call_outcome do not inspect
     gas_obs. No msg.gas expression is present in this proposed statement.
     Source fixed indexing, read/type, arithmetic, and write likewise do
     not consume gas observations. Thus a finite defining-clause proof
     of replay invariance (with gas_obs framed) is available once the
     concrete expression/program is fixed. It is NOT yet proved here.
   - If msg.gas were used, next_gas_reading on [] raises
     Error (RuntimeError "msg.gas: no gas reading"); on w::ws it returns
     IntV(w2n w). This error is not exempt, but the value may affect calls;
     success for just one observation list would not suffice.
   - Actual ExtCall failures: operand/address/calldata checks raise
     TypeError, frame_call_value/check_not_static can raise RuntimeError
     "write in static context", precheck raises RuntimeError
     "ExtCall target has no code", take_call_outcome may raise RuntimeError
     "take_call_outcome" or "call outcome accounts", unsuccessful outcome
     raises RevertData. These are not the exempt runtime errors.
   - RETURN DECODING IS IMPORTANT: evaluate_abi_decode_return delegates to
     evaluate_abi_decode_returndata, which may return "abi_decode invalid";
     lift_sum_runtime turns this into RuntimeError. This error IS exempt
     when tops contains a dynamic ABI-decode target. Thus the candidate
     must check actual valid ABI-zero return bytes (and every replay),
     or establish absence of dynamic ABI-decode targets. Cannot declare
     all external-call errors non-exempt from the call's Uint return type.
     "decode return unwrap" is non-exempt. No conversion builtin in the
     proposed statement can yield "convert empty bytes to signed".

   Decision: no target_case canonicality exclusion was found; universal
   admission has a precise admitted route above. Candidate remains OPEN.
   Remaining concrete obligations are program/body/layout/state/code/gas
   witnesses and actual path/store success listed in the continuation
   probe, plus observation-framed execution of the no-msg.gas statement
   with valid ABI-zero return bytes. source_replay_excludes_gas_exempt_cert
   is the checked reusable boundary; its premise is not added to the
   frozen theorem and has not been established for a concrete program.
*)
