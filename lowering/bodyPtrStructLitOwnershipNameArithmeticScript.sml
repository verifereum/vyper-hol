Theory bodyPtrStructLitOwnershipNameArithmetic
Ancestors bodyPtrStructLitOwnershipBaseCases bodyPtrStructLitOwnershipNumeric
  bodyPtrStructLitOwnershipConsumers bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeProps
  exprLowering compileEnv context gasShadowCompileBase

Theorem alloc_run_compile_addmod_names:
  alloc_run fresh_outputs (compile_addmod_names ce rt aty a bty b mty m)
    (\v s. fresh_outputs s)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_addmod_names_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_name_vv,
      SRULE [SF ETA_ss] alloc_run_unwrap_value] >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all (SRULE [alloc_run_def] alloc_run_compile_addmod) >> simp[]
QED

Theorem alloc_run_compile_mulmod_names:
  alloc_run fresh_outputs (compile_mulmod_names ce rt aty a bty b mty m)
    (\v s. fresh_outputs s)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_mulmod_names_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_name_vv,
      SRULE [SF ETA_ss] alloc_run_unwrap_value] >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all (SRULE [alloc_run_def] alloc_run_compile_mulmod) >> simp[]
QED

Theorem alloc_run_compile_powmod256_names:
  alloc_run fresh_outputs (compile_powmod256_names ce rt aty a bty b)
    (\v s. fresh_outputs s)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_powmod256_names_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_name_vv,
      SRULE [SF ETA_ss] alloc_run_unwrap_value] >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all (SRULE [alloc_run_def] alloc_run_compile_pow_mod256) >> simp[]
QED

Theorem alloc_run_expr_addmod_names:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty
      (Builtin rt AddMod [Name aty a; Name bty b; Name mty m])) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_addmod_names >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_expr_mulmod_names:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty
      (Builtin rt MulMod [Name aty a; Name bty b; Name mty m])) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_mulmod_names >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_expr_powmod256_names:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty
      (Builtin rt PowMod256 [Name aty a; Name bty b])) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_powmod256_names >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED
