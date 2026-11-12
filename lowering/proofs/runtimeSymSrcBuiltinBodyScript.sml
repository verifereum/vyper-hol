Theory runtimeSymSrcBuiltinBody
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission supportedTypes
  runtimeSymSrcInterfaces exprCallBounds list supportedExprTraverse exprLowering
  supportedExprs supportedExprForms context compileEnv venomInst vyperAST
  memoryValueDefs typedCopyDomain builtinMisc builtinBytes builtinSimple

Theorem runtime_sym_builtin_child:
  (!e ty. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce ty e) /\
  EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args /\ MEM e args ==>
  (!ty. runtime_sym_expr_contract tops cfn ce ty e) /\
  supported_expr tops e /\ ~supported_expr_exists is_self_code e
Proof
  rpt strip_tac
  >- (first_x_assum irule >> metis_tac[expr_list_member_bound])
  >- metis_tac[runtime_sym_supported_argument]
  >> gvs[supported_exprs_exists_every, EVERY_MEM]
QED

Theorem runtime_sym_builtin_env[local]:
  runtime_sym_generator_contracts tops ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty (Env item) args
Proof
  strip_tac >> drule runtime_sym_generators_expr_primitive >>
  disch_then (assume_tac o cj 2 o SRULE [runtime_sym_expr_primitive_clauses_def]) >>
  pure_rewrite_tac[runtime_sym_builtin_contract_def] >> rpt strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, compile_builtin_dispatch_body_def, as_stack_val_def] >>
  Cases_on `compile_env_var item s` >>
  simp[NoAsms, as_stack_val_def] >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  simp[runtime_sym_value_def]
QED
Theorem runtime_sym_builtin_lower_value:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) /\
  runtime_sym_env ce /\ EVERY (supported_pure_expr tops) args /\
  ~supported_exprs_exists is_self_code args ==>
  !e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value cfn ce t e s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> drule runtime_sym_generators_lower_value >>
  pure_rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  rpt strip_tac >> drule_all runtime_sym_builtin_child >> strip_tac >>
  qpat_x_assum `!cfn ce ty e s op s'. _` (drule_at_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac) >>
  simp[]
QED


Theorem runtime_sym_builtin_body:
  runtime_sym_generator_contracts tops /\
  (!e t. expr_size e < list_size expr_size args ==>
     runtime_sym_expr_contract tops cfn ce t e) ==>
  runtime_sym_builtin_contract tops (compile_builtin_dispatch_body cfn) ce rt ty bi args
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_builtin_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) args /\
   ~supported_exprs_exists is_self_code args` by
    gvs[runtime_sym_builtin_domain, supported_expr_exists_def] >>
  `!e t s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce t e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     drule_all runtime_sym_builtin_lower_value >> simp[]) >>
  Cases_on `bi`
  >~ [`Bop bop`] >- suspend "bop"
  >> cheat
QED
Resume runtime_sym_builtin_body[bop]:
  drule runtime_sym_bop_selections >> strip_tac >>
  namedCases_on `args` ["", "a tail"] >> gnvs[] >>
  namedCases_on `tail` ["", "b rest"] >> gnvs[] >>
  FAIL_TAC "bop probe"
QED
Finalise runtime_sym_builtin_body
