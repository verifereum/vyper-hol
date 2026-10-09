(*
 * Vyper-to-Venom Lowering Correctness (Top-Level)
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Connects Vyper big-step semantics (call_external) to Venom IR
 * execution (run_context) on the raw lower_vyper_runtime_unit context.
 *
 * Three-layer decomposition:
 *   Layer 1 - Selector dispatch: calldata method_id routes to correct
 *     entry block (selectorDispatch, per compile_selector_dispatch)
 *   Layer 2 - Argument decoding: ABI-encoded calldata decoded to values
 *     matching tx.args (abiEncoderProps, valueEncodingProofs)
 *   Layer 3 - Function body: compiled Venom body preserves semantics
 *     (stmtLoweringProps, exprLoweringProps)
 *
 * TOP-LEVEL:
 *   venom_env_rel, initial_venom_state_rel -- PLAN 5.7 entry boundary
 *   external_call_result_rel, source_unit_execution_correct -- oracle boundary
 *   lower_vyper_runtime_unit_correct -- S1 (planned admission, Milestone 6)
 *   lower_vyper_runtime_unit_source_unit_ok -- S2 (Milestone 5)
 *   lower_vyper_runtime_unit_memory_ok -- S3 (Milestone 5)
 *
 * Legacy NONE-mode result definition retained explicitly until TASK056.
 * STATUS: S1-S3 are statements, NOT proved correctness certificates.
 * Before major proof repair, check lowering definitions against the chosen
 * upstream compiler target; see docs/compiler-definition-parity.md.
 *)

Theory vyperLoweringCorrect
Ancestors
  vyperCompiler
  selectorDispatch
  moduleLoweringProps
  stmtLoweringProps
  exprLoweringProps
  valueEncodingProofs
  builtinProps
  contextProps
  arithmeticProps
  abiEncoderProps
  vyperInterpreter vyperEntryCompat
  vyperContext
  venomExecSemantics
  venomState
  compileEnv e2eDefs supportedProgram compileVyper
  unitTransformDefs unitShapeDefs

(* ===== Cross-Domain Result Relation ===== *)

(* Observable state produced by an external source call. Function-local scope
   state is gone at this boundary, so this is intentionally smaller than
   compileEnv$state_rel but still includes all externally visible effects. *)
Definition external_logs_rel_def:
  external_logs_rel cenv (addr : address) (am : abstract_machine) ss ⇔
    LIST_REL (log_entry_equiv cenv addr) am.logs ss.vs_logs
End

Definition external_call_state_rel_def:
  external_call_state_rel cenv cx (am : abstract_machine) ss ⇔
    ss.vs_accounts = am.accounts ∧
    ss.vs_transient = am.tStorage ∧
    external_logs_rel cenv cx.txn.target am ss ∧
    call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx
End

(* Relates Vyper external call results to Venom execution results.
   call_external_simple projects the NONE-mode result to
   (value + exception, abstract_machine). No oracle-mode bridge is claimed.
   run_context returns exec_result.

   Parameterized by tenv (type environment), cenv/cx (the lowering
   state relation context), and ret_type (return type) for ABI encoding
   of the return value.

   Success case requires the external-call state relation, so logs,
   accounts, transient storage, call context, and returndata are all part
   of the lowering result relation instead of e2e-side patches. *)
(* TASK051 compatibility: the original NONE-mode result contract, unchanged
   except its explicit name. No old/new semantic bridge. Removal TASK056. *)
Definition external_call_result_rel_legacy_def:
  (* Successful return *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INL v, am') (Halt ss') <=>
    cenv.ce_type_env = tenv /\
    external_call_state_rel cenv cx am' ss' /\
    (?abi_val.
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ss'.vs_returndata =
        enc (vyper_to_abi_type tenv ret_type) abi_val)) /\
  (* Assert/revert => Abort revert *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (AssertException _), am')
                             (Abort Revert_abort ss') <=> T) /\
  (* Vyper error => any Venom abort or error *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (Error _), am')
                             (Abort _ ss') <=> T) /\
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (Error _), am')
                             (Error _) <=> T) /\
  (* All other combinations are invalid *)
  (external_call_result_rel_legacy _ _ _ _ _ _ <=> F)
End

(* ===== PLAN 5.7 oracle-mode boundary ===== *)

(* No gas-reading/oracle equality is invented here: cc_gas, outcomes,
   code/labels and frame-pointer fields are deliberately free at entry. *)
Definition venom_env_rel_def:
  venom_env_rel tx vs <=>
    compileEnv$call_ctx_rel tx vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx /\
    ~vs.vs_call_ctx.cc_static /\
    vs.vs_tx_ctx.tc_blobhashes = tx.blob_hashes /\
    vs.vs_prev_hashes = tx.block_hashes /\
    (!n. vs.vs_block_ctx.bc_blockhash n =
         let idx = tx.block_number - n - 1 in
         if n < tx.block_number /\ tx.block_number - 256 <= n /\
            idx < LENGTH tx.block_hashes
         then EL idx tx.block_hashes else 0w)
End

Definition initial_venom_state_rel_def:
  initial_venom_state_rel am tx vs <=>
    value_transfer_ok tx am.accounts /\
    vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
    tx_env_ok tx /\ venom_env_rel tx vs /\
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ vs.vs_memory = [] /\
    vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0 /\
    vs.vs_returndata = [] /\ vs.vs_requests = []
End

(* Only success compares effects/requests. Runtime failure must abort, except
   the exact dynamic strict-decoding exemption on Halt. Error (stuck or fuel
   exhaustion), OK and IntRet are never acceptable results, even if exempt. *)
Definition external_call_result_rel_def:
  external_call_result_rel tops ret tx (res, am', rqs) vres <=>
    case (res, vres) of
      (INL v, Halt ss) =>
        return_bytes tops ret v ss.vs_returndata /\
        ss.vs_accounts = am'.accounts /\ ss.vs_transient = am'.tStorage /\
        logs_correspond (compiled_event_info tops) (type_env tops)
          tx.target am'.logs ss.vs_logs /\
        ss.vs_requests = rqs
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error (RuntimeError m)), Abort _ _) => T
    | (INR (Error e), Halt _) => decode_strictness_exempt tops e
    | _ => F
End

Definition source_unit_execution_correct_def:
  source_unit_execution_correct tops ret am tx unit vs <=>
    ?fuel. external_call_result_rel tops ret tx
             (call_external (SOME vs.vs_outcomes) am tx)
             (run_context fuel unit.cu_context vs)
End

(* ===== Planned lowering stages (NOT certificates) ===== *)

(* S1: planned admission, Milestone 6. Proof idea: supported syntax induction,
   selector/argument decoding, body simulation with the threaded oracle and
   requests; canonical wrapped returns and runtime-check aborts. *)
Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  cheat
QED

(* S2: planned admission, Milestone 5. Proof idea: lowering's checked context
   and supported function/loop restrictions establish the raw O1 shape. *)
Theorem lower_vyper_runtime_unit_source_unit_ok:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops
    ==> o1_source_unit_ok unit
Proof
  cheat
QED

(* S3: planned admission, Milestone 5. Proof idea: allocation-budget and
   buffer-layout induction bound each reachable raw memory access. Excluding
   source_exempt is essential: dynamic decoding can read unchecked offsets. *)
Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) am tx)
    ==> raw_unit_memory_ok unit.cu_context vs
Proof
  cheat
QED

(* ===== Superseded admission provenance ===== *)
(* TASK051 full-token consumer audit found no source consumer of
   vyper_to_venom_correct. Its original statement/proof below is INACTIVE,
   retained for provenance only, not saved and not an extra admission.


(* For a well-formed external call to a compiled module:

   If calldata correctly encodes a call to function tx.function_name
   with arguments tx.args, then Venom execution on the lowered context
   produces a result corresponding to Vyper evaluation.

   ctx is bound to run_lowering_pair_compat on the given compilation inputs.
   The selector_matches predicate links sel_num to tx.function_name
   via keccak256 of the ABI signature. *)
Theorem vyper_to_venom_correct:
  !tenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    vs am tx sel fn_lbl htz cenv
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering_pair_compat selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    (* tx targets a known external function *)
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    (* Calldata encodes the call *)
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      vs.vs_call_ctx.cc_calldata /\
    (* Selector table entry matches function *)
    MEM (sel, fn_lbl, htz) selectors /\
    selector_matches sel tx.function_name
      (vyper_to_abi_types tenv (MAP SND args)) /\
    (* Venom state is initial *)
    vs.vs_inst_idx = 0
    ==>
    ?fuel.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name))
        ret (call_external_simple am tx) (run_context fuel ctx vs)
Proof
  cheat
QED
*)
