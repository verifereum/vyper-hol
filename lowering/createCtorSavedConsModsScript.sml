(* A saved head is transported across the actual successful suffix. *)
Theory createCtorSavedConsMods
Ancestors
  createCtorSavedCons createExprSizeExitDefsMods
  bodyFullExtCallPosList bodyFullExtCallPosTransport bodyFullExtCallPosAggregate
  bodyInvCodeProps targetPureWalkSource vyperMachineFrame exprSimWordArgs
  allocaSiteResource freshWrites vyperStorageFootprint vyperStorageTrace
  exprLoweringProps wordArgsPtr stateRelProj list exprSimProps
  loweringPosts compileEnv vyperInterpreter vyperState exprSimMemDefs bodyPtrDefs
  exprLowering venomState loweringStateRelDefs context bodyFullExtCallSavedOperand
  ptrDiscipline exprSimUnwrap

Theorem ctor_saved_rows_cons_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ expr_body_pre_mods mods cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv cut /\
  ci_mono sa cut /\ ci_mono cut sb /\ u.vs_labels = t.vs_labels /\
  (!K. dead_lo_ok_mods K (DF K) lo cenv cx) /\
  EVERY (source_body_call_supported cx)
    (int_calls_exprs xs) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := out) /\
  (!K. valid_horizon cx st0 K es.storage_trace ==>
       stmt_state_rel K ctx func cenv cx es s0) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       valid_horizon cx st0 K es.storage_trace) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
         xs [e] [sv] sa cut es s0 G0 tn0 K (INL [v]) mid G1 tn1 t) /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
       extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
         [] xs svs cut sb mid t G1 tn1 K (INL vs) ee G2 tn2 u) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  extcall_positional_post_mods mods T DF lo d ctx func cenv cx env
    [] (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs)) ee G2 tn2 u
Proof
  cheat
QED
