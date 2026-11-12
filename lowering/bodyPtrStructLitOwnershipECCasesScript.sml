Theory bodyPtrStructLitOwnershipECCases
Ancestors bodyPtrStructLitOwnershipEC bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipMemory
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering
  compileEnv context list pair

Theorem alloc_run_builtin_ecrecover:
  4 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty ECRecover args) (\v s. T)
Proof
  strip_tac >>
  `MEM (HD args) args /\ MEM (EL 1 args) args /\
   MEM (EL 2 args) args /\ MEM (EL 3 args) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
     Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  rpt (simp[SF ETA_ss] >> irule alloc_run_bind >>
    qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
    (reverse conj_tac
    >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
        qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
        first_x_assum irule >> simp[])) >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rename1 `shape_state last` >>
  `fresh_outputs last` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  drule_all (SRULE [alloc_run_def] alloc_run_compile_ecrecover) >> simp[]
QED

Theorem alloc_run_builtin_ecadd:
  2 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty ECAdd args) (\v s. T)
Proof
  strip_tac >>
  `MEM (HD args) args /\ MEM (EL 1 args) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  ntac 2 (simp[SF ETA_ss] >> irule alloc_run_bind >>
     qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
     (reverse conj_tac
     >- (irule alloc_run_conseq >>
         irule_at Any (Q.INST [`R` |-> `\s. T`, `ce` |-> `ce`]
           alloc_run_struct_child_frame) >>
         qexists `internal` >> simp[shape_stable_def] >>
         qexists `ce` >> simp[] >> first_x_assum irule >> simp[])) >>
     gen_tac >> simp[] >> irule alloc_run_bind >>
     qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
     (reverse conj_tac
     >- (irule alloc_run_conseq >>
         irule_at Any (Q.INST [`R` |-> `\s. cenv_shape_ok s ce`]
           alloc_run_unwrap_value_frame) >>
         simp[cenv_shape_ok_stable])) >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> rename1 `shape_state last` >>
  `fresh_outputs last` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  drule_all (SRULE [alloc_run_def] alloc_run_compile_ecadd_points) >> simp[]
QED

Theorem alloc_run_builtin_ecmul:
  2 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty ECMul args) (\v s. T)
Proof
  strip_tac >>
  `MEM (HD args) args /\ MEM (EL 1 args) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_struct_child_frame) >>
      qexists `internal` >> simp[shape_stable_def] >>
      qexists `ce` >> simp[] >> first_x_assum irule >> simp[])) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. cenv_shape_ok s ce`]
        alloc_run_unwrap_value_frame) >> simp[cenv_shape_ok_stable])) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      first_x_assum irule >> simp[])) >>
  gen_tac >> simp[alloc_run_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> rename1 `shape_state last` >>
  `fresh_outputs last` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  drule_all (SRULE [alloc_run_def] alloc_run_compile_ecmul_point) >> simp[]
QED

Theorem alloc_run_builtin_ec:
  ((bi = ECRecover /\ 4 <= LENGTH args) \/
   (bi = ECAdd /\ 2 <= LENGTH args) \/
   (bi = ECMul /\ 2 <= LENGTH args)) /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty bi args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  metis_tac[alloc_run_builtin_ecrecover, alloc_run_builtin_ecadd,
    alloc_run_builtin_ecmul]
QED
