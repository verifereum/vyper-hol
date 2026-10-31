(*
 * Expression simulation: calls (#636, Calls)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the call targets
 * but internal calls.  Proved: send (compile_send_sim, by exprSimSend's
 * compile_send_case_sim, row 2 of #636's Calls table).  Cheated, for the
 * later #636 PRs, by row of that table:
 *   1 extcall/staticcall in SOME oracle mode, including reverts and
 *     default_return_value (#553): compile_extcall_sim
 *   3 raw_call (#554): compile_raw_call_sim; raw_call of msg.data:
 *     compile_raw_call_calldata_sim
 *   4 raw_log, raw_revert, selfdestruct: compile_raw_log_sim,
 *     compile_raw_revert_sim, compile_selfdestruct_sim
 *   5 the creates: compile_create_sim
 *
 * Unprovable as the definitions stand (for compile_raw_call_sim,
 * compile_raw_call_calldata_sim and compile_create_sim, once
 * expr_sim_pre's exclusion of them, below, is lifted):
 *   - compile_raw_call_sim, compile_raw_log_sim, compile_selfdestruct_sim
 *     and compile_create_sim: compile_call lowers RawCallTarget, RawLog,
 *     SelfDestructTarget and CreateTarget to INVALID (builtinCreate's
 *     compile_create_* are not called yet), where the source can succeed.
 *   - compile_raw_call_calldata_sim, and the create lowerings once they are
 *     wired in: they allocate with DALLOCA, at vs_fmp, which
 *     stmt_state_rel does not relate to the ALLOCA allocations, so
 *     expr_post's memory frame does not follow (#668, #636 Infrastructure
 *     row 2).
 *   - compile_create_sim, once the create lowerings are wired in, for a
 *     second reason: a create stores its run's pending deletions in the
 *     source (eval_create), which state_rel's accounts_rel requires empty,
 *     while Venom's create result (extract_venom_result) drops them.
 *
 * expr_sim_pre excludes raw_call and the creates (~expr_has_evm_run e),
 * since the source runs them on the EVM even with the outcome oracle, so
 * compile_raw_call_sim, compile_raw_call_calldata_sim and
 * compile_create_sim hold vacuously for now; they stay cheated until that
 * exclusion is lifted.
 *
 * Internal calls (row 6) have no lemma: expr_sim_pre excludes them
 * (int_calls_expr e = []) until #638 states the INVOKE hypothesis.
 *)

Theory exprSimCalls
Ancestors
  list exprSim exprSimHyps exprSimSend vyperAST

Theorem compile_extcall_sim:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  cheat
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
  cheat
QED

Theorem compile_raw_call_calldata_sim:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallCalldataTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  cheat
QED

Theorem compile_raw_log_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
Proof
  cheat
QED

Theorem compile_raw_revert_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawRevert) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawRevert) args dflt)
Proof
  cheat
QED

Theorem compile_selfdestruct_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (SelfDestructTarget) args dflt)) ==>
    expr_vv_ok cenv (Call ann (SelfDestructTarget) args dflt)
Proof
  cheat
QED

Theorem compile_create_sim:
  !cenv ann kind has_salt rof args dflt.
    expr_sim_below cenv (expr_size (Call ann (CreateTarget kind has_salt rof) args dflt)) ==>
    expr_vv_ok cenv (Call ann (CreateTarget kind has_salt rof) args dflt)
Proof
  cheat
QED
