Theory runtimeSymSrcExpressions
Ancestors
  runtimeSymSrcExprBody runtimeSymSrcBuiltinBody runtimeSymSrcTypeBuiltinBody
  runtimeSymSrcGeneratorContracts runtimeSymSrcInterfaces runtimeSymSrcEmission
  exprLowering exprCallBounds venomInst stackPlanTypes

Triviality symbolic_invalid_expr_call:
  EVERY runtime_sym_inst (state_insts s) /\ invalid_expr_call ty s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  simp[invalid_expr_call_def] >> pairarg_tac >>
  simp[] >> strip_tac >> gvs[runtime_sym_value_def, is_label_operand_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  simp[runtime_sym_inst_def, mk_inst_def]
QED

fun symbolic_child_tac equation induction_hypothesis inputs =
  qmatch_assum_rename_tac equation >>
  qpat_assum induction_hypothesis (qspecl_then inputs mp_tac) >>
  (impl_tac >- (qpat_assum `_ < _` mp_tac >> Omega.OMEGA_TAC)) >>
  disch_then (qspecl_then [`child_val`, `child_end`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  strip_tac >> asm_rewrite_tac [];

val symbolic_expr_child_tac =
  symbolic_child_tac `compile_expr child_env child_ty child child_st = (child_val,child_end)`
    `!ex ce ty st. _ ==> !v st'. _` [`child`, `child_env`, `child_ty`, `child_st`];

val symbolic_guarded_child_cases =
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >> pure_rewrite_tac[] >> strip_tac
  >>~- ([`invalid_expr_call _ _ = _`], drule_all symbolic_invalid_expr_call >> simp[]);

Theorem runtime_sym_expression_pointwise[local]:
  runtime_sym_generator_contracts tops ==>
  ((!ce ty e s. !v s'. runtime_sym_env tops ce /\
      (supported_expr tops e \/ supported_place_expr tops e \/
       supported_effect_place_expr tops e) /\
      ~supported_expr_exists is_self_code e /\
      EVERY runtime_sym_inst (state_insts s) /\ compile_expr ce ty e s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
   (!ce rt ty bi args s. !v s'. runtime_sym_env tops ce /\
      supported_expr tops (Builtin rt bi args) /\
      ~supported_expr_exists is_self_code (Builtin rt bi args) /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_builtin_dispatch ce rt ty bi args s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v) /\
   (!ce vt ty tb rt args s. !v s'. runtime_sym_env tops ce /\
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
    `cfn` |-> `expr_child_callback (expr_size e + cenv_defaults_size ce) compile_expr`,
    `bfn` |-> `builtin_child_callback (expr_size e + cenv_defaults_size ce)
      compile_builtin_dispatch`,
    `tfn` |-> `type_child_callback (expr_size e + cenv_defaults_size ce)
      compile_type_builtin_dispatch`]
    runtime_sym_expr_body) >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
      simp[NoAsms, runtime_sym_expr_contract_def, runtime_sym_builtin_contract_def,
           runtime_sym_type_builtin_contract_def] >> rpt gen_tac >> strip_tac >>
      symbolic_guarded_child_cases >>
      FIRST
        [symbolic_expr_child_tac,
         symbolic_child_tac
           `compile_builtin_dispatch child_env child_rt child_ty child_bi child_args child_st = (child_val,child_end)`
           `!args ce rt ty bi st. _ ==> !v st'. _`
           [`child_args`, `child_env`, `child_rt`, `child_ty`, `child_bi`, `child_st`],
         symbolic_child_tac
           `compile_type_builtin_dispatch child_env child_vt child_ty child_tb child_rt child_args child_st = (child_val,child_end)`
           `!args ce vt ty tb rt st. _ ==> !v st'. _`
           [`child_args`, `child_env`, `child_vt`, `child_ty`, `child_tb`, `child_rt`, `child_st`]]) >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >> disch_then assume_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  pure_rewrite_tac[GSYM (SIMP_RULE pure_ss [COND_CLAUSES]
    (CONV_RULE (DEPTH_CONV ETA_CONV) compile_expr_raw_def))] >>
  metis_tac[]
QED

Resume runtime_sym_expression_pointwise[builtin]:
  mp_tac (Q.INST [
    `cfn` |-> `expr_child_callback
      (list_size expr_size args + cenv_defaults_size ce) compile_expr`]
    runtime_sym_builtin_body) >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      simp[runtime_sym_expr_contract_def] >> rpt gen_tac >> strip_tac >>
      symbolic_expr_child_tac) >>
  pure_rewrite_tac[runtime_sym_builtin_contract_def] >> disch_then assume_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  pure_rewrite_tac[GSYM (SIMP_RULE pure_ss [COND_CLAUSES]
    (CONV_RULE (DEPTH_CONV ETA_CONV) compile_expr_raw_def))] >>
  metis_tac[]
QED

Resume runtime_sym_expression_pointwise[typebuiltin]:
  mp_tac (Q.INST [
    `cfn` |-> `expr_child_callback
      (list_size expr_size args + cenv_defaults_size ce) compile_expr`]
    runtime_sym_type_builtin_body) >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      simp[runtime_sym_expr_contract_def] >> rpt gen_tac >> strip_tac >>
      symbolic_expr_child_tac) >>
  pure_rewrite_tac[runtime_sym_type_builtin_contract_def] >> disch_then assume_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  pure_rewrite_tac[GSYM (SIMP_RULE pure_ss [COND_CLAUSES]
    (CONV_RULE (DEPTH_CONV ETA_CONV) compile_expr_raw_def))] >>
  metis_tac[]
QED

Finalise runtime_sym_expression_pointwise

Theorem runtime_sym_expression_contracts:
  runtime_sym_generator_contracts tops ==>
  ((!ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e) /\
   (!ce rt ty bi args.
      runtime_sym_builtin_contract tops compile_builtin_dispatch ce rt ty bi args) /\
   (!ce vt ty tb rt args.
      runtime_sym_type_builtin_contract tops compile_type_builtin_dispatch
        ce vt ty tb rt args))
Proof
  pure_rewrite_tac[runtime_sym_expr_contract_def,
    runtime_sym_builtin_contract_def, runtime_sym_type_builtin_contract_def] >>
  metis_tac[runtime_sym_expression_pointwise]
QED
