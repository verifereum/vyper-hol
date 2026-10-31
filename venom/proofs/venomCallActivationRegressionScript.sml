(* Activated dispatch counterexamples: independent of old preservation owners.
 * The retained 074 regression's historical comments describe its pre-activation
 * baseline; those helper witnesses do not substitute for these dispatch tests. *)
Theory venomCallActivationRegression
Ancestors
  venomCallOracleRegression venomExecSemantics venomCallOracleDefs
  venomState venomInst extCallOracle stateFrame words list
Libs
  wordsLib

val () = augment_srw_ss [wordsLib.SIZES_ss, wordsLib.WORD_GROUND_ss];

Definition probe_call_def:
  probe_call target = mk_inst 0 CALL
    [Lit 7w; Lit target; Lit 0w; Lit 0w; Lit 1w; Lit 1w; Lit 3w]
    ["result"]
End

val dispatch_defs =
  [probe_call_def, call_probe_state_def, call_probe_request_def,
   call_probe_outcome_def, init_venom_state_def, empty_call_context_def,
   venom_call_request_def, read_memory_def, consume_call_outcome_def,
   take_outcome_def, computed_precompile_addresses, record_request_def,
   failed_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def,
   write_memory_with_expansion_def,
   update_var_def, lookup_var_def, mk_inst_def, step_inst_base_def,
   exec_ext_call_def, eval_operand_def, w2w_n2w];

(* Dispatcher retains evaluation/arity obligations; the completion helper
   has no alternate dispatch. This equation is also used by focused probes. *)
Theorem probe_call_dispatch:
  step_inst_base (probe_call target) s =
    OK (update_var "result"
      (FST (consume_call_outcome (venom_call_request s target 0w 0w 1w
         s.vs_call_ctx.cc_static) 1 3 s))
      (SND (consume_call_outcome (venom_call_request s target 0w 0w 1w
         s.vs_call_ctx.cc_static) 1 3 s)))
Proof
  simp[probe_call_def, mk_inst_def, step_inst_base_def, eval_operand_def,
       exec_ext_call_def]
QED

Theorem activated_call_not_preservation:
  let s = call_probe_state with vs_outcomes := [failed_outcome call_probe_request]
  in ?t. step_inst_base (probe_call 8w) s = OK t /\
         t.vs_outcomes <> s.vs_outcomes /\ t.vs_requests <> s.vs_requests
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_call_vs_nop:
  let s = call_probe_state with vs_outcomes := [failed_outcome call_probe_request]
  in ?t. step_inst_base (probe_call 8w) s = OK t /\
         step_inst_base (mk_inst 1 NOP [] []) s = OK s /\
         execution_frame s = execution_frame s /\
         t.vs_outcomes <> s.vs_outcomes /\ t.vs_requests <> s.vs_requests
Proof
  `!s. step_inst_base (mk_inst 1 NOP [] []) s = OK s` by
    simp[mk_inst_def, step_inst_base_def] >>
  mp_tac activated_call_not_preservation >> simp[LET_THM]
QED

Theorem activated_ordinary_success_short_write:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome]
  in ?t. step_inst_base (probe_call 8w) s = OK t /\
    lookup_var "result" t = SOME 1w /\ t.vs_outcomes = [] /\
    t.vs_requests = [call_probe_request] /\ t.vs_returndata = [9w] /\
    t.vs_memory = [1w; 9w; 3w; 4w] /\
    t.vs_accounts = call_probe_outcome.co_accounts /\
    t.vs_transient = call_probe_outcome.co_tStorage /\
    t.vs_logs = call_probe_outcome.co_logs
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_failed_short_write:
  let s = call_probe_state with vs_outcomes :=
    [call_probe_outcome with co_success := F]
  in ?t. step_inst_base (probe_call 8w) s = OK t /\
    lookup_var "result" t = SOME 0w /\ t.vs_outcomes = [] /\
    t.vs_requests = [call_probe_request] /\ t.vs_returndata = [9w] /\
    t.vs_memory = [1w; 9w; 3w; 4w] /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_exhausted:
  ?t. step_inst_base (probe_call 8w) call_probe_state = OK t /\
    lookup_var "result" t = SOME 0w /\ t.vs_outcomes = [] /\
    t.vs_requests = [call_probe_request] /\ t.vs_returndata = [] /\
    t.vs_memory = call_probe_state.vs_memory /\
    t.vs_accounts = call_probe_state.vs_accounts /\
    t.vs_transient = call_probe_state.vs_transient /\
    t.vs_logs = call_probe_state.vs_logs
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_inherited_static:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
    vs_call_ctx := empty_call_context with cc_static := T |>;
    rq = venom_call_request s 8w 0w 0w 1w F
  in ?t. step_inst_base (probe_call 8w) s = OK t /\
    rq.cr_static /\ lookup_var "result" t = SOME 1w /\
    t.vs_outcomes = [] /\ t.vs_requests = [rq] /\
    t.vs_returndata = [9w] /\ t.vs_memory = [1w; 9w; 3w; 4w] /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_staticcall_zero_value:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
    rq = venom_call_request s 8w 0w 0w 1w T;
    inst = mk_inst 1 STATICCALL [Lit 7w; Lit 8w; Lit 0w; Lit 1w; Lit 1w; Lit 3w]
      ["result"]
  in ?t. step_inst_base inst s = OK t /\
    rq.cr_static /\ rq.cr_value = 0 /\ lookup_var "result" t = SOME 1w /\
    t.vs_outcomes = [] /\ t.vs_requests = [rq] /\ t.vs_returndata = [9w] /\
    t.vs_memory = [1w; 9w; 3w; 4w] /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Definition probe_computed_def:
  probe_computed target sz = mk_inst 0 CALL
    [Lit 7w; Lit target; Lit 0w; Lit 0w; Lit sz; Lit 1w; Lit 0w] ["result"]
End

Theorem probe_computed_dispatch[local]:
  step_inst_base (probe_computed target sz) s =
    OK (update_var "result"
      (FST (consume_call_outcome
        (venom_call_request s target 0w 0w sz s.vs_call_ctx.cc_static) 1 0 s))
      (SND (consume_call_outcome
        (venom_call_request s target 0w 0w sz s.vs_call_ctx.cc_static) 1 0 s)))
Proof
  simp[probe_computed_def, mk_inst_def, step_inst_base_def,
       eval_operand_def, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> simp[]
QED

val computed_defs =
  [probe_computed_def, call_probe_state_def, init_venom_state_def,
   empty_call_context_def, step_inst_base_def, mk_inst_def, eval_operand_def,
   exec_ext_call_def, venom_call_request_def, read_memory_def,
   consume_call_outcome_def, take_outcome_def,
   record_request_def, computed_precompile_def, adopt_outcome_def,
   adopt_outcome_deletions_def,
   failed_outcome_def, write_memory_with_expansion_def,
   lookup_var_def, update_var_def, w2w_n2w,
   precompile_result_empty_ecrecover, precompile_result_empty_ec,
   precompile_result_invalid_ec, byteTheory.LENGTH_word_to_bytes,
   finite_mapTheory.FLOOKUP_UPDATE];

Theorem call_probe_state_static[local,simp]:
  ~call_probe_state.vs_call_ctx.cc_static
Proof
  simp[call_probe_state_def, init_venom_state_def, empty_call_context_def]
QED

Theorem activated_computed_ecrecover:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
    vs_requests := [call_probe_request] |>
  in step_inst_base (probe_computed 1w 0w) s =
    OK (update_var "result" 1w (s with vs_returndata := []))
Proof
  simp computed_defs
QED

Theorem activated_computed_sha256:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
    vs_requests := [call_probe_request] |>
  in ?t. step_inst_base (probe_computed 2w 0w) s = OK t /\
    lookup_var "result" t = SOME 1w /\ LENGTH t.vs_returndata = 32 /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs
Proof
  simp computed_defs
QED

Theorem activated_computed_empty_ec:
  let s = call_probe_state with <| vs_outcomes := [call_probe_outcome];
    vs_requests := [call_probe_request] |>
  in step_inst_base (probe_computed 6w 0w) s =
       OK (update_var "result" 1w (s with vs_returndata := REPLICATE 64 0w)) /\
     step_inst_base (probe_computed 7w 0w) s =
       OK (update_var "result" 1w (s with vs_returndata := REPLICATE 64 0w))
Proof
  mp_tac consume_computed_empty_ec >>
  simp[Excl "consume_call_outcome_eq", LET_THM] >> strip_tac >>
  simp[Excl "consume_call_outcome_eq", probe_computed_dispatch]
QED

Theorem consume_empty_return_size[local]:
  consume_call_outcome rq ro ret_size s = (word, t) ==>
  t.vs_returndata = [] ==>
  !new_size. consume_call_outcome rq ro new_size s = (word, t)
Proof
  rpt strip_tac >>
  `(FST (take_outcome rq s.vs_outcomes)).co_returnData = []` by
    (qpat_x_assum `consume_call_outcome _ _ _ _ = _`
       (mp_tac o AP_TERM ``\p:bytes32 # venom_state. (SND p).vs_returndata``) >>
     PURE_REWRITE_TAC[consume_call_outcome_eq] >> simp[]) >>
  `consume_call_outcome rq ro new_size s = consume_call_outcome rq ro ret_size s` by
    (PURE_REWRITE_TAC[consume_call_outcome_eq] >> simp[]) >>
  gvs[Excl "consume_call_outcome_eq"]
QED

Theorem consume_invalid_ec_zero_output[local]:
  s = call_probe_state with <|
        vs_memory := REPLICATE 63 0w ++ [1w];
        vs_outcomes := [call_probe_outcome]; vs_requests := [call_probe_request] |> ==>
  consume_call_outcome (venom_call_request s 6w 0w 0w 64w F) 1 0 s =
       (0w, s with vs_returndata := []) /\
     consume_call_outcome (venom_call_request s 7w 0w 0w 64w F) 1 0 s =
       (0w, s with vs_returndata := [])
Proof
  disch_then SUBST1_TAC >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] consume_computed_invalid_ec) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >> conj_tac >>
  irule consume_call_outcome_empty_output_size >>
  simp[Excl "consume_call_outcome_eq"] >>
  qexists_tac `3` >> simp[Excl "consume_call_outcome_eq"]
QED

Theorem activated_computed_invalid_ec:
  let s = call_probe_state with <|
    vs_memory := REPLICATE 63 0w ++ [1w];
    vs_outcomes := [call_probe_outcome]; vs_requests := [call_probe_request] |>
  in step_inst_base (probe_computed 6w 64w) s =
       OK (update_var "result" 0w (s with vs_returndata := [])) /\
     step_inst_base (probe_computed 7w 64w) s =
       OK (update_var "result" 0w (s with vs_returndata := []))
Proof
  `call_probe_state.vs_call_ctx.cc_static = F` by
    simp[call_probe_state_def, init_venom_state_def, empty_call_context_def] >>
  simp[probe_computed_dispatch, Excl "consume_call_outcome_eq",
       consume_invalid_ec_zero_output]
QED

Theorem activated_nonzero_precompile_ordinary:
  let s = call_probe_state with <|
    vs_outcomes := [call_probe_outcome; failed_outcome call_probe_request];
    vs_requests := [call_probe_request] |>;
    rq = venom_call_request s 2w 1w 0w 1w F;
    inst = mk_inst 1 CALL
      [Lit 7w; Lit 2w; Lit 1w; Lit 0w; Lit 1w; Lit 1w; Lit 3w] ["result"]
  in ?t. step_inst_base inst s = OK t /\ lookup_var "result" t = SOME 1w /\
    t.vs_outcomes = [failed_outcome call_probe_request] /\
    t.vs_requests = [call_probe_request; rq] /\ t.vs_returndata = [9w] /\
    t.vs_memory = [1w; 9w; 3w; 4w]
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_actual_length_expansion:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome];
    inst = (probe_call 8w) with inst_operands :=
      [Lit 7w; Lit 8w; Lit 0w; Lit 0w; Lit 1w; Lit 5w; Lit 3w]
  in ?t. step_inst_base inst s = OK t /\
    t.vs_memory = [1w; 2w; 3w; 4w; 0w; 9w] /\ LENGTH t.vs_memory = 6
Proof
  simp dispatch_defs >> EVAL_TAC
QED

Theorem activated_gas_value_ignored:
  step_inst_base (probe_call 8w) s =
  step_inst_base ((probe_call 8w) with inst_operands :=
    [Lit 999w; Lit 8w; Lit 0w; Lit 0w; Lit 1w; Lit 1w; Lit 3w]) s
Proof
  simp[probe_call_def, mk_inst_def, step_inst_base_def, eval_operand_def,
       exec_ext_call_def]
QED

Theorem activated_gas_expression_evaluated:
  step_inst_base ((probe_call 8w) with inst_operands :=
    [Var "missing"; Lit 8w; Lit 0w; Lit 0w; Lit 1w; Lit 1w; Lit 3w])
    call_probe_state = Error "undefined operand"
Proof
  simp dispatch_defs
QED

Theorem activated_output_arity:
  step_inst_base ((probe_call 8w) with inst_outputs := []) s =
    Error "ext_call requires single output" /\
  step_inst_base ((probe_call 8w) with inst_outputs := ["a"; "b"]) s =
    Error "ext_call requires single output"
Proof
  simp[probe_call_def, mk_inst_def, step_inst_base_def, eval_operand_def,
       exec_ext_call_def]
QED

Theorem activated_unequal_targets:
  let s = call_probe_state with vs_outcomes := [call_probe_outcome]
  in ?t1 t2. step_inst_base (probe_call 8w) s = OK t1 /\
             step_inst_base (probe_call 9w) s = OK t2 /\
             t1.vs_outcomes = t2.vs_outcomes /\
             t1.vs_requests <> t2.vs_requests
Proof
  mp_tac unequal_targets_not_transport >>
  simp[Excl "consume_call_outcome_eq", LET_THM, probe_call_dispatch,
       update_var_def]
QED
