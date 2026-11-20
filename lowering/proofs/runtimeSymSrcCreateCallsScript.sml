Theory runtimeSymSrcCreateCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcCallStaging runtimeSymSrcAbiEncode
  runtimeSymSrcContext runtimeSymSrcContextTypedBase
  exprLowering compileEnv emitHelper list stackPlanTypes supportedExprs

(* The current supported-program whitelist rejects every creation target. *)
Theorem runtime_sym_call_create:
  !tops cfn ce rt ty ck has_salt rof metadata es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env tops ce /\
    supported_expr tops (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    ~supported_expr_exists is_self_code
       (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (CreateTarget ck has_salt rof metadata)
      es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `default` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED
