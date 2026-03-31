(*
 * Vyper-to-Venom Lowering Correctness (Top-Level)
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Connects Vyper big-step semantics (call_external) to Venom IR
 * execution (run_context) on the context produced by run_lowering.
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
 *   external_call_result_rel -- cross-domain result relation
 *   vyper_to_venom_correct   -- lowering preserves execution semantics
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
  vyperSmallStep
  vyperInterpreter
  vyperContext
  venomExecSemantics
  venomState

(* ===== Cross-Domain Result Relation ===== *)

(* Relates Vyper external call results to Venom execution results.
   call_external returns (value + exception, abstract_machine).
   run_context returns exec_result.

   Parameterized by tenv (type environment) and ret_type (return type)
   for ABI encoding of the return value.

   Success case requires:
   - returndata = ABI encoding of the return value
   - accounts (contract storage, balances) match
   - transient storage matches

   Log correspondence uses logs_correspond to bridge Vyper's
   log list (nsid # value list) to Venom's event list
   (logger # topics # data). The conversion involves ABI encoding
   of topic values and data layout -- defined in e2eCorrectness. *)
Definition external_call_result_rel_def:
  (* Successful return *)
  (external_call_result_rel tenv ret_type (INL v, am') (Halt ss') <=>
    (?abi_val.
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ss'.vs_returndata =
        enc (vyper_to_abi_type tenv ret_type) abi_val) /\
    ss'.vs_accounts = am'.accounts /\
    ss'.vs_transient = am'.tStorage) /\
  (* Assert/revert => Abort revert *)
  (external_call_result_rel tenv ret_type (INR (AssertException _), am')
                             (Abort Revert_abort ss') <=> T) /\
  (* Vyper error => any Venom abort or error *)
  (external_call_result_rel tenv ret_type (INR (Error _), am')
                             (Abort _ ss') <=> T) /\
  (external_call_result_rel tenv ret_type (INR (Error _), am')
                             (Error _) <=> T) /\
  (* All other combinations are invalid *)
  (external_call_result_rel _ _ _ _ <=> F)
End

(* ===== Lowering Correctness ===== *)

(* For a well-formed external call to a compiled module:

   If calldata correctly encodes a call to function tx.function_name
   with arguments tx.args, then Venom execution on the lowered context
   produces a result corresponding to Vyper evaluation.

   ctx is bound to run_lowering on the given compilation inputs.
   The selector_matches predicate links sel_num to tx.function_name
   via keccak256 of the ABI signature. *)
Theorem vyper_to_venom_correct:
  !tenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes entry_label
    vs am tx sel fn_lbl htz
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes entry_label in
    (* tx targets a known external function *)
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx) am
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
      external_call_result_rel tenv ret
        (call_external am tx)
        (run_context fuel ctx vs)
Proof
  cheat
QED
