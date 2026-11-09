(*
 * Expression simulation: calls (#636, Calls)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the call targets
 * but internal calls.  Proved: send (compile_send_sim, by exprSimSend's
 * compile_send_case_sim, row 2 of #636's Calls table), and, vacuously,
 * the creates and selfdestruct (compile_create_sim,
 * compile_selfdestruct_sim: expr_sim_pre excludes them, below).
 * Each other lemma is its piece in a leaf theory exprSimCall*, by row of
 * that table:
 *   1 extcall/staticcall in SOME oracle mode, including reverts and
 *     default_return_value (#553): compile_extcall_sim
 *   3 raw_call (#554): compile_raw_call_sim; raw_call of msg.data:
 *     compile_raw_call_calldata_sim
 *   4 raw_log, raw_revert: compile_raw_log_sim, compile_raw_revert_sim
 *
 * Unprovable as the definitions stand (for raw_call and the creates, once
 * expr_sim_pre's exclusion of them, below, is lifted):
 *   - compile_raw_log_sim and compile_selfdestruct_sim:
 *     compile_call lowers RawLog and SelfDestructTarget to
 *     INVALID, where
 *     the source can succeed.
 *   - compile_raw_call_sim and compile_raw_call_calldata_sim with
 *     is_delegate_call: both sides run the EVM, but differently: the source
 *     (run_delegate_call) dispatches a precompile address to
 *     dispatch_precompiles and fails unless ext_call_success_accounts_ok,
 *     while Venom's DELEGATECALL (exec_delegatecall) runs the target's
 *     account code with neither, so a delegate call to a precompile
 *     returns the precompile's output in the source and empty success in
 *     Venom.
 *   - compile_raw_call_calldata_sim, and the create lowerings: they allocate with DALLOCA, at vs_fmp, which
 *     stmt_state_rel does not relate to the ALLOCA allocations, so
 *     expr_post's memory frame does not follow (#668, #636 Infrastructure
 *     row 2).
 *
 * A call or staticcall raw_call takes its outcome from the oracle, as the
 * lowered CALL/STATICCALL does.  expr_sim_pre excludes delegate raw_calls
 * and the creates (~expr_has_evm_run e), since the source runs them on the
 * EVM even with the outcome oracle, and selfdestruct, until the source's
 * selfdestruct halts; so those cases hold vacuously.
 *
 * Internal calls (row 6) have no lemma: expr_sim_pre excludes them
 * (int_calls_expr e = []) until #638 states the INVOKE hypothesis.
 *)

Theory exprSimCalls
Ancestors
  list  exprSimHyps exprSimSend vyperAST
  exprSimCallExtcall exprSimCallRawCall exprSimCallRawCallCalldata
  exprSimCallRawLog exprSimCallRawRevert

Theorem compile_extcall_sim:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  ACCEPT_TAC extcall_expr_vv_ok
QED

Theorem compile_send_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
Proof
  ACCEPT_TAC compile_send_case_sim
QED

Theorem compile_raw_call_sim:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallTarget flags) args dflt)
Proof
  ACCEPT_TAC raw_call_expr_vv_ok
QED

Theorem compile_raw_call_calldata_sim:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallCalldataTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  ACCEPT_TAC raw_call_calldata_expr_vv_ok
QED

Theorem compile_raw_log_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
Proof
  ACCEPT_TAC raw_log_expr_vv_ok
QED

Theorem compile_raw_revert_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawRevert) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawRevert) args dflt)
Proof
  ACCEPT_TAC raw_revert_expr_vv_ok
QED

Theorem compile_selfdestruct_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (SelfDestructTarget) args dflt)) ==>
    expr_vv_ok cenv (Call ann (SelfDestructTarget) args dflt)
Proof
  rw[exprSimHypsDefsTheory.expr_vv_ok_def,
     exprSimHypsDefsTheory.expr_sim_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED

Theorem compile_create_sim:
  !cenv ann kind has_salt rof order args dflt.
    expr_sim_below cenv (expr_size (Call ann (CreateTarget kind has_salt rof order) args dflt)) ==>
    expr_vv_ok cenv (Call ann (CreateTarget kind has_salt rof order) args dflt)
Proof
  rw[exprSimHypsDefsTheory.expr_vv_ok_def,
     exprSimHypsDefsTheory.expr_sim_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED
