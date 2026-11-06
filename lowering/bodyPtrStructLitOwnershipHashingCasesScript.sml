Theory bodyPtrStructLitOwnershipHashingCases
Ancestors bodyPtrStructLitOwnershipHashing bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering
  compileEnv context list pair

Theorem alloc_run_builtin_hashing:
  (bi = Keccak256 \/ bi = Sha256) /\ 1 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty bi args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[] >>
  TRY (rename1 `~is_bytestring_type aty` >>
       Cases_on `aty` >> simp[] >>
       TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
            TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[]))) >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> Cases_on `args` >> gvs[])) >>
  gen_tac >> simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `fresh_outputs st` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_compile_keccak256_word,
    SRULE [alloc_run_def] alloc_run_compile_keccak256_bytes,
    SRULE [alloc_run_def] alloc_run_compile_keccak256_bytesm,
    SRULE [alloc_run_def] alloc_run_compile_sha256_word,
    SRULE [alloc_run_def] alloc_run_compile_sha256_bytes,
    SRULE [alloc_run_def] alloc_run_compile_sha256_bytesm]
QED
