Theory bodyPtrStructLitOwnershipBodyClosure
Ancestors bodyPtrStructLitOwnershipExprBody bodyPtrStructLitOwnershipRawCreate
  bodyPtrStructLitOwnershipTypeCases bodyPtrStructLitOwnershipAbiType
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeDefs
  exprLowering supportedExprTraverse compileEnv context vyperAST list

Theorem alloc_run_compile_type_builtin_dispatch_body_cases:
  type_builtin_arity tb <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args) (\v s. T)
Proof
  strip_tac >> Cases_on `tb` >>
  TRY (irule (Q.INST [`internal` |-> `F`] alloc_run_type_builtin_nonabi) >> simp[] >> NO_TAC)
  >- (irule (Q.INST [`internal` |-> `F`] alloc_run_type_builtin_decode) >>
      gvs[type_builtin_arity_def]) >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_type_builtin_encode) >> simp[]
QED

Theorem alloc_run_compile_expr_body_closed:
  ~supported_expr_exists expr_shape_root e /\
  (!env req child. supported_expr_exists (\x. x = child) e /\
     ~supported_expr_exists expr_shape_root child ==>
     shape_step F compiler_label (\s. cenv_shape_ok s env)
       (cfn env req child) (\v s. value_shape_ok s v) /\
     alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
       (cfn env req child) (\v s. T)) /\
  (!ann bi args. e = Builtin ann bi args ==>
     alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
       (bfn ce (expr_type e) ty bi args) (\v s. T)) /\
  (!ann tb target args. e = TypeBuiltin ann tb target args ==>
     alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
       (tfn ce (expr_type e) ty tb target args) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty e) (\v s. T)
Proof
  strip_tac >> irule alloc_run_compile_expr_body_cases >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_call >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  gvs[supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  conj_tac >- metis_tac[] >> disj2_tac >> disj1_tac >>
  qexists `e` >> simp[] >> irule supported_expr_exists_root >> simp[]
QED
