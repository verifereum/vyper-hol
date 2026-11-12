Theory exprSimAbiEncodeArgsLayoutContracts
Ancestors
  exprSimAbiEncodeArgsLayoutProbe supportedProgram exprSimHypsDefs
  exprSimDefs vyperTypeCallGraph supportedDecls supportedTypes

Definition layout_call_def:
  layout_call = Call layout_wide (IntCall (NONE,"f")) [] NONE
End

Definition layout_abi_def:
  layout_abi = TypeBuiltin (BaseT (BytesT (Dynamic 320))) (AbiEncode T NONE)
    (TupleT [layout_wide]) [layout_call]
End

Theorem layout_singleton_cases:
  exprs_case F ctx func ce cx [layout_call] <=>
  (!env ty es. expr_body_pre ce cx env layout_call es ==>
    expr_sim ctx func ce cx ty layout_call es) /\
  (!env ty es. expr_body_pre ce cx env layout_call es ==>
    expr_vv_sim ctx func ce cx ty layout_call es)
Proof
  simp[exprs_case_def, expr_sim_case_def, expr_vv_case_def]
QED

Theorem layout_narrow_not_supported_return:
  ~supported_return_type tops layout_narrow
Proof
  EVAL_TAC
QED

Theorem layout_narrow_header_excluded:
  ~supported_declaration_header tops
    (FunctionDecl Internal mut nr rr name args dflts layout_narrow (stmts:stmt list))
Proof
  simp[supported_declaration_header_def, supported_function_return_def,
       layout_narrow_not_supported_return]
QED

Theorem layout_narrow_declaration_excluded:
  supported_program tops ==>
  ~MEM (FunctionDecl Internal mut nr rr name args dflts layout_narrow (stmts:stmt list)) tops
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       listTheory.EVERY_MEM] >> metis_tac[layout_narrow_header_excluded]
QED

Theorem layout_body_pre_contract:
  expr_body_pre ce cx env layout_abi es <=>
    expr_sim_inv ce cx env es /\ well_typed_expr env layout_abi /\
    byte_widths_expr layout_abi /\ alloc_limits_expr ce layout_abi /\
    call_evaluation_safe cx [(NONE,"f")] /\
    ~expr_has_evm_run layout_abi /\
    ~supported_expr_exists call_operands_effect_root layout_abi /\
    (?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
       IS_SOME (supported_function_decl tops (NONE,"f") Internal)) /\
    (!target. supported_expr_exists (expr_abi_decode_target_root target) layout_abi ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))
Proof
  simp[expr_body_pre_def, layout_abi_def, layout_call_def,
       int_calls_expr_def]
QED
