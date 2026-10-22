(* TASK051 focused PLAN 5.7 checks. These proofs use definitions only, never
   S1-S3 or old stage admissions. They are boundary checks, not simulations. *)
Theory loweringBoundaryChecks
Ancestors
  vyperLoweringCorrect e2eDefs compileEnv
  venomExecSemantics venomState venomInst vyperState vyperValue vyperABI
  stmtLoweringProps exprLoweringProps emitHelperProps
  stateFrame list

(* The strengthened relation requires oracle mode and exact request prefixes.
   Reuse existing frame-preserving update proofs; no per-field API matrix. *)
Theorem statement_oracle_boundary:
  state_rel cenv cx es ss ==>
  es.outcomes = SOME ss.vs_outcomes /\ es.requests = ss.vs_requests /\
  state_rel cenv cx es (update_var name w ss)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >- fs[state_rel_def] >>
  conj_tac >- fs[state_rel_def] >>
  irule state_rel_update_var >> simp[]
QED

Theorem statement_rejects_none_oracle:
  ~state_rel cenv cx (es with outcomes := NONE) ss
Proof
  simp[state_rel_def]
QED

Theorem statement_assert_boundary:
  result_rel tv cenv cx (INR (AssertException reason), es)
    (Abort Revert_abort ss) /\
  (result_rel tv cenv cx (INR (AssertException reason), es)
    (Abort ExHalt_abort ss) <=> reason = "UNREACHABLE")
Proof
  simp[result_rel_def]
QED

(* Fuel exhaustion or malformed dispatch cannot witness the clean obligation,
   even when the source strict-decoding failure is exempt. *)
Theorem lowering_rejects_nonterminal:
  ~external_call_result_rel tops ret tx src (Error msg) /\
  ~external_call_result_rel tops ret tx src (OK ss) /\
  ~external_call_result_rel tops ret tx src (IntRet ir ss)
Proof
  PairCases_on `src` >> Cases_on `src0`
  >- simp[external_call_result_rel_def] >>
  rename1 `external_call_result_rel _ _ _ (INR exc,_,_) _` >> Cases_on `exc` >>
  simp[external_call_result_rel_def] >>
  rename1 `vyperState$Error err` >> Cases_on `err` >>
  simp[external_call_result_rel_def]
QED

Theorem lowering_real_termination:
  external_call_result_rel tops ret tx src vres ==>
  (?ss. vres = Halt ss) \/ (?kind ss. vres = Abort kind ss)
Proof
  Cases_on `vres` >> simp[lowering_rejects_nonterminal]
QED

Theorem lowering_run_context_zero_error:
  !ctx vs. ?e. run_context 0 ctx vs = Error e
Proof
  rpt gen_tac >> Cases_on `ctx.ctx_entry`
  >- simp[run_context_def] >>
  rename1 `ctx.ctx_entry = SOME entry` >>
  Cases_on `venomInst$lookup_function entry ctx.ctx_functions`
  >- simp[run_context_def] >>
  rename1 `venomInst$lookup_function entry ctx.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn`
  >- simp[run_context_def, run_function_def] >>
  simp[run_context_def, run_function_def, Once run_blocks_def]
QED

Theorem lowering_zero_fuel_rejected:
  ~external_call_result_rel tops ret tx src (run_context 0 ctx vs)
Proof
  qspecl_then [`ctx`, `vs`] strip_assume_tac lowering_run_context_zero_error >>
  simp[lowering_rejects_nonterminal]
QED

Theorem lowering_stuck_entry_rejected:
  unit.cu_context.ctx_entry = NONE ==>
  ~source_unit_execution_correct tops ret am tx unit vs
Proof
  simp[source_unit_execution_correct_def, run_context_def,
       lowering_rejects_nonterminal]
QED

Theorem lowering_source_execution_terminates:
  source_unit_execution_correct tops ret am tx unit vs ==>
  ?fuel. 0 < fuel /\
    ((?ss. run_context fuel unit.cu_context vs = Halt ss) \/
     (?kind ss. run_context fuel unit.cu_context vs = Abort kind ss))
Proof
  rw[source_unit_execution_correct_def] >>
  qexists_tac `fuel` >> conj_tac
  >- (Cases_on `fuel` >> gvs[lowering_zero_fuel_rejected]) >>
  drule lowering_real_termination >> simp[]
QED

(* Assert reasons, including ordinary raise "UNREACHABLE", may REVERT;
   INVALID may correspond only to the distinguished unreachable exception. *)
Theorem lowering_assert_boundary:
  external_call_result_rel tops ret tx (INR (AssertException s), am, rqs)
    (Abort Revert_abort ss) /\
  (external_call_result_rel tops ret tx (INR (AssertException s), am, rqs)
    (Abort ExHalt_abort ss) <=> s = "UNREACHABLE")
Proof
  simp[external_call_result_rel_def]
QED

Theorem lowering_runtime_boundary:
  external_call_result_rel tops ret tx (INR (Error (RuntimeError msg)), am, rqs)
    (Abort kind ss) /\
  (external_call_result_rel tops ret tx (INR (Error (RuntimeError msg)), am, rqs)
    (Halt ss) <=> decode_strictness_exempt tops (RuntimeError msg)) /\
  ~external_call_result_rel tops ret tx (INR (Error (TypeError msg)), am, rqs)
    (Abort kind ss) /\
  ~external_call_result_rel tops ret tx (INR (Error (TypeError msg)), am, rqs)
    (Halt ss)
Proof
  Cases_on `kind` >> simp[external_call_result_rel_def, decode_strictness_exempt_def]
QED

(* A failed external call re-raises the callee's revert data: it may only
   REVERT. *)
Theorem lowering_revert_data_boundary:
  external_call_result_rel tops ret tx (INR (Error (RevertData bs)), am, rqs)
    (Abort Revert_abort ss) /\
  ~external_call_result_rel tops ret tx (INR (Error (RevertData bs)), am, rqs)
    (Abort ExHalt_abort ss) /\
  ~external_call_result_rel tops ret tx (INR (Error (RevertData bs)), am, rqs)
    (Halt ss)
Proof
  simp[external_call_result_rel_def, decode_strictness_exempt_def]
QED

Theorem lowering_decode_exemption_narrow:
  decode_strictness_exempt tops e ==>
  e = RuntimeError "abi_decode invalid" /\
  ?ty. occurs_abi_decode_target ty tops /\
       is_dynamic (vyper_to_abi_type (type_env tops) ty)
Proof
  simp[decode_strictness_exempt_def]
QED

Theorem lowering_static_decode_not_exempt:
  (!ty. occurs_abi_decode_target ty tops ==>
        ~is_dynamic (vyper_to_abi_type (type_env tops) ty)) ==>
  ~external_call_result_rel tops ret tx
    (INR (Error (RuntimeError "abi_decode invalid")), am, rqs) (Halt ss)
Proof
  simp[external_call_result_rel_def, decode_strictness_exempt_def] >> metis_tac[]
QED

Theorem lowering_success_boundary:
  external_call_result_rel tops ret tx (INL v, am, rqs) (Halt ss) <=>
  return_bytes tops ret v ss.vs_returndata /\
  ss.vs_accounts = am.accounts /\ ss.vs_transient = am.tStorage /\
  logs_correspond (compiled_event_info tops) (type_env tops)
    tx.target am.logs ss.vs_logs /\ ss.vs_requests = rqs
Proof
  simp[external_call_result_rel_def]
QED

Theorem lowering_wrapped_return:
  needs_external_call_wrap ret /\ ret <> NoneT ==>
  (external_call_result_rel tops ret tx (INL v, am, rqs) (Halt ss) <=>
   (?abi_v. vyper_to_abi (type_env tops) ret v = SOME abi_v /\
     ss.vs_returndata =
       enc (Tuple [vyper_to_abi_type (type_env tops) ret]) (ListV [abi_v])) /\
   ss.vs_accounts = am.accounts /\ ss.vs_transient = am.tStorage /\
   logs_correspond (compiled_event_info tops) (type_env tops)
     tx.target am.logs ss.vs_logs /\ ss.vs_requests = rqs)
Proof
  simp[lowering_success_boundary, return_bytes_def]
QED

(* A concrete successful terminal witness with requests, and a distinct
   request list rejected. Leftover outcomes are intentionally unconstrained. *)
Theorem lowering_none_return_witness:
  external_call_result_rel tops NoneT tx (INL v, am, rqs)
    (Halt (ss with <| vs_accounts := am.accounts; vs_transient := am.tStorage;
       vs_logs := am.logs; vs_returndata := []; vs_requests := rqs |>))
Proof
  simp[lowering_success_boundary, return_bytes_def, logs_correspond_def] >>
  irule LIST_REL_refl >> simp[log_entry_corresponds_def]
QED

Theorem lowering_success_requests_exact:
  external_call_result_rel tops ret tx (INL v, am, rqs) (Halt ss) /\
  rqs' <> rqs ==>
  ~external_call_result_rel tops ret tx (INL v, am, rqs)
    (Halt (ss with vs_requests := rqs'))
Proof
  simp[lowering_success_boundary]
QED

Theorem lowering_abort_requests_free:
  external_call_result_rel tops ret tx
    (INR (Error (RuntimeError msg)), am, rqs)
    (Abort kind (ss with <| vs_requests := rqs'; vs_outcomes := os |>))
Proof
  Cases_on `kind` >> simp[external_call_result_rel_def]
QED

(* Actual positive-fuel executions, not an identity/stuck substitute. *)
Definition lowering_probe_context_def:
  lowering_probe_context opc ops =
    mk_venom_context
      [mk_raw_function "entry"
        [<| bb_label := "entry";
            bb_instructions := [mk_inst 0 opc ops []] |>]] (SOME "entry")
End

Theorem lowering_probe_terminates:
  (?ss'. run_context 1 (lowering_probe_context STOP []) ss = Halt ss' /\
         ss'.vs_returndata = []) /\
  (?ss'. run_context 1 (lowering_probe_context REVERT [Lit 0w; Lit 0w]) ss =
         Abort Revert_abort ss') /\
  (?ss'. run_context 1 (lowering_probe_context INVALID []) ss =
         Abort ExHalt_abort ss')
Proof
  rpt conj_tac >>
  simp[lowering_probe_context_def, mk_venom_context_def, mk_raw_function_def,
       run_context_def, run_function_def, venomInstTheory.lookup_function_def,
       fn_entry_label_def, entry_block_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, mk_inst_def,
       eval_phis_def, phi_prefix_length_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[Once step_inst_def, step_inst_base_def, halt_state_def,
       set_returndata_def, revert_state_def, read_memory_def, eval_operand_def]
QED

(* Environment/initial entry stay independent of Venom's ordinary GAS value,
   arbitrary outcome list and the raw unit's unobserved source fields. *)
Theorem lowering_initial_gas_oracle_free:
  initial_venom_state_rel am tx vs ==>
  initial_venom_state_rel am tx
    (vs with <| vs_outcomes := os;
      vs_call_ctx := vs.vs_call_ctx with cc_gas := gas |>)
Proof
  simp[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def]
QED

Theorem lowering_initial_requests_empty:
  initial_venom_state_rel am tx vs ==> vs.vs_requests = []
Proof
  simp[initial_venom_state_rel_def]
QED
