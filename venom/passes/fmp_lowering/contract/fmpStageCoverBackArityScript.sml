(* Unconditional source INVOKE arity boundary for backward coverage. *)
Theory fmpStageCoverBackArity
Ancestors
  fmpStageCoverBackArityPrep fmpStageCoverBackCfgArity

Theorem fmp_stage_source_invoke_user_arity:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label name::args /\
  lookup_function name C.ctx_functions = SOME callee ==>
  LENGTH (fn_user_param_insts callee) <= LENGTH args
Proof
  strip_tac >>
  irule fmp_stage_source_invoke_user_arity_conditional >>
  metis_tac[fmp_cfg_normalization_user_count]
QED
