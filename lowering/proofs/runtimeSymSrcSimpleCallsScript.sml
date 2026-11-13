Theory runtimeSymSrcSimpleCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv emitHelper loweringShapeDefs list venomInst stackPlanTypes
  supportedExprs supportedExprTraverse

Theorem runtime_sym_call_log:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt RawLog es default) /\
    ~supported_expr_exists is_self_code (Call rt RawLog es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) RawLog es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `rt` >> Cases_on `default` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem runtime_sym_call_revert:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt RawRevert es default) /\
    ~supported_expr_exists is_self_code (Call rt RawRevert es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) RawRevert es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `rt` >> Cases_on `default` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem runtime_sym_call_selfdestruct:
  !cfn ce rt ty es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt SelfDestructTarget es default) /\
    ~supported_expr_exists is_self_code (Call rt SelfDestructTarget es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) SelfDestructTarget es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `rt` >> Cases_on `default` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem runtime_sym_supported_send[local]:
  supported_expr tops (Call rt (Send has_gas) es default) ==>
  rt = NoneT /\ default = NONE /\
  ((~has_gas /\ ?a b. es = [a;b] /\ supported_pure_expr tops a /\
                                      supported_pure_expr tops b) \/
   (has_gas /\ ?a b c. es = [a;b;c] /\ supported_pure_expr tops a /\
                   supported_pure_expr tops b /\ supported_pure_expr tops c))
Proof
  Cases_on `rt` >> Cases_on `default` >> Cases_on `has_gas` >>
  simp[supported_expr_def, supported_pure_expr_def] >>
  Cases_on `es` >> simp[supported_effect_expr_def] >>
  rename1 `addr::rest` >> Cases_on `rest` >> simp[supported_effect_expr_def] >>
  rename1 `addr::amount::rest` >> Cases_on `rest` >> simp[supported_effect_expr_def] >>
  rename1 `addr::amount::gas::rest` >> Cases_on `rest` >> simp[supported_effect_expr_def]
QED

Theorem runtime_sym_call_send:
  runtime_sym_lower_value_clause tops ==>
  !cfn ce rt ty has_gas es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops (Call rt (Send has_gas) es default) /\
    ~supported_expr_exists is_self_code (Call rt (Send has_gas) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (Send has_gas) es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> drule runtime_sym_supported_send >> strip_tac >>
  gvs[compile_call_def, supported_expr_exists_def, runtime_sym_value_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (qpat_assum `!cfn ce ty e s op s'. _`
    (dxrule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
    simp[supported_expr_def] >> strip_tac) >>
  gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  simp[runtime_sym_value_def, is_label_operand_def] >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]
QED
