Theory runtimeSymSrcExpressions
Ancestors
  runtimeSymSrcExprBody runtimeSymSrcBuiltinBody runtimeSymSrcTypeBuiltinBody
  runtimeSymSrcGeneratorContracts runtimeSymSrcInterfaces exprLowering exprCallBounds

Theorem runtime_sym_expression_pointwise[local]:
  runtime_sym_generator_contracts tops ==>
  ((!ce ty e s. !v s'. runtime_sym_env ce /\
      (supported_expr tops e \/ supported_place_expr tops e \/
       supported_effect_place_expr tops e) /\
      ~supported_expr_exists is_self_code e /\
      EVERY runtime_sym_inst (state_insts s) /\ compile_expr ce ty e s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
   (!ce rt ty bi args s. !v s'. runtime_sym_env ce /\
      supported_expr tops (Builtin rt bi args) /\
      ~supported_expr_exists is_self_code (Builtin rt bi args) /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_builtin_dispatch ce rt ty bi args s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
   (!ce vt ty tb rt args s. !v s'. runtime_sym_env ce /\
      supported_expr tops (TypeBuiltin vt tb rt args) /\
      ~supported_expr_exists is_self_code (TypeBuiltin vt tb rt args) /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_type_builtin_dispatch ce vt ty tb rt args s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v))
Proof
  strip_tac >> ho_match_mp_tac compile_expr_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >- suspend "typebuiltin"
QED

Resume runtime_sym_expression_pointwise[expr]:
  mp_tac (Q.INST [
    `cfn` |-> `expr_child_callback (expr_size e) compile_expr`,
    `bfn` |-> `builtin_child_callback (expr_size e) compile_builtin_dispatch`,
    `tfn` |-> `type_child_callback (expr_size e) compile_type_builtin_dispatch`]
    runtime_sym_expr_body) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
      simp[NoAsms, runtime_sym_expr_contract_def, runtime_sym_builtin_contract_def,
           runtime_sym_type_builtin_contract_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
      IF_CASES_TAC >> pure_rewrite_tac[] >> strip_tac >> metis_tac[]) >>
  simp[runtime_sym_expr_contract_def] >> disch_then irule >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Resume runtime_sym_expression_pointwise[builtin]:
  mp_tac (Q.INST [
    `cfn` |-> `expr_child_callback (list_size expr_size args) compile_expr`]
    runtime_sym_builtin_body) >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      simp[runtime_sym_expr_contract_def] >> metis_tac[]) >>
  simp[runtime_sym_builtin_contract_def] >> disch_then irule >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Resume runtime_sym_expression_pointwise[typebuiltin]:
  mp_tac (Q.INST [
    `cfn` |-> `expr_child_callback (list_size expr_size args) compile_expr`]
    runtime_sym_type_builtin_body) >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      simp[runtime_sym_expr_contract_def] >> metis_tac[]) >>
  simp[runtime_sym_type_builtin_contract_def] >> disch_then irule >>
  simp[Once compile_expr_raw_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Finalise runtime_sym_expression_pointwise
