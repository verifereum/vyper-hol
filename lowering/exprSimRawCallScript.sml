(*
 * Expression simulation: raw_call (#636, Calls row 3)
 *
 * raw_call(to, data, [value=], [gas=], [max_outsize=], [is_static_call=],
 * [revert_on_failure=]) lowers (compile_call's RawCallTarget clause) to
 * the address with lower_value, the data unwrapped to memory, the value=
 * and gas= keyword operands in source order, GAS without gas=, the output
 * buffer (compile_raw_call_outbuf) and the call (compile_raw_call_finish).
 * In oracle mode a non-delegate source raw_call takes the same outcome as
 * the lowered CALL/STATICCALL (eval_raw_call's take_call_outcome and
 * adopt_call_outcome; extCallOracleStep's exec_ext_call_oracle_step).
 * expr_sim_pre and expr_body_pre exclude delegate raw_calls and raw_calls
 * without revert_on_failure (~expr_has_evm_run), so those hold vacuously.
 *
 * TOP-LEVEL:
 *   compile_raw_call_case — raw_call's expr_sim_case and expr_vv_case from
 *     its operands' exprs_case, for compile_expr_sim and the body
 *     simulation
 *)

Theory exprSimRawCall
Ancestors
  allocLimits
  list pair vyperMisc fragExec loweringSlice exprSim exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper compileEnv localPtrsProps valueEncoding
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState exprSimSend
Libs
  pairLib

(* TOP-LEVEL *)
Theorem compile_raw_call_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
Proof
  cheat
QED
