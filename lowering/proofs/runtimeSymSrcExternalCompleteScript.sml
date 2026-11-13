Theory runtimeSymSrcExternalComplete
Ancestors
  runtimeSymSrcExternalPrimitive runtimeSymSrcExternalCalls
  runtimeSymSrcInterfaces runtimeSymSrcGeneratorContracts exprLowering context
  emitHelper venomInst stackPlanTypes supportedExprs supportedExprTraverse list

Theorem runtime_sym_call_external:
  (!dst src info s v s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!dst src hi info s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand hi /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  runtime_sym_multi_vvs_clause tops /\ runtime_sym_lower_value_clause tops ==>
  !cfn ce rt ty static skip fname ats ret opts es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
      runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\
    supported_expr tops (Call rt (ExtCall static skip (fname,ats,ret) opts) es default) /\
    ~supported_expr_exists is_self_code
      (Call rt (ExtCall static skip (fname,ats,ret) opts) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (ExtCall static skip (fname,ats,ret) opts)
      es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> mp_tac runtime_sym_external_call_kwargs_cond >>
  (impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> disch_tac >>
  mp_tac runtime_sym_call_external_cond >>
  (impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
