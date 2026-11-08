Theory bodyPtrStructLitOwnershipExprBody
Ancestors bodyPtrStructLitOwnershipBaseCases bodyPtrStructLitOwnershipNameArithmetic
  bodyPtrStructLitOwnershipConstructors bodyPtrStructLitOwnershipIfexpCase
  bodyPtrStructLitOwnershipSubscript bodyPtrStructLitOwnershipAttribute
  bodyPtrStructLitOwnershipPop bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness
  loweringShapeDefs loweringShapeProps exprLowering supportedExprTraverse
  context compileEnv gasShadowCompileBase vyperAST list

Theorem alloc_run_compile_expr_body_cases:
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
       (tfn ce (expr_type e) ty tb target args) (\v s. T)) /\
  (!ann target args default_ret. e = Call ann target args default_ret ==>
     alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
       (compile_call cfn ce (expr_type e) ty target args default_ret) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty e) (\v s. T)
Proof
  Cases_on `e` >> simp[alloc_run_expr_body_literal, alloc_run_expr_body_name,
    alloc_run_expr_body_flag_member, alloc_run_expr_body_top_level_name]
  >- suspend "ifexp"
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "pop"
  >> suspend "call"
QED

Resume alloc_run_compile_expr_body_cases[ifexp]:
  simp[supported_expr_exists_def] >> strip_tac >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_compile_expr_body_ifexp) >>
  rpt conj_tac >>
  FIRST [first_assum (irule o cj 1), first_assum (irule o cj 2)] >>
  simp[] >>
  `!z:expr. supported_expr_exists (\x. x = z) z` by
    (gen_tac >> irule supported_expr_exists_root >> simp[]) >> metis_tac[]
QED
Resume alloc_run_compile_expr_body_cases[subscript]:
  simp[supported_expr_exists_def] >> strip_tac >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_expr_subscript) >>
  rpt conj_tac >> rpt gen_tac >>
  FIRST [first_assum (irule o cj 1), first_assum (irule o cj 2)] >> simp[] >>
  `!z:expr. supported_expr_exists (\x. x = z) z` by
    (gen_tac >> irule supported_expr_exists_root >> simp[]) >> metis_tac[]
QED
Resume alloc_run_compile_expr_body_cases[attribute]:
  simp[supported_expr_exists_def] >> strip_tac >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_expr_attribute) >>
  rpt conj_tac >>
  FIRST [first_assum (irule o cj 1), first_assum (irule o cj 2)] >> simp[] >>
  disj2_tac >> irule supported_expr_exists_root >> simp[]
QED
Resume alloc_run_compile_expr_body_cases[structlit]:
  simp[supported_expr_exists_def, supported_fields_exists_every, EXISTS_MEM] >>
  strip_tac >> irule alloc_run_expr_structlit >> rpt strip_tac >>
  FIRST [first_assum (irule o cj 1), first_assum (irule o cj 2)] >> simp[] >>
  `!z:expr. supported_expr_exists (\x. x = z) z` by
    (gen_tac >> irule supported_expr_exists_root >> simp[]) >>
  metis_tac[pairTheory.SND]
QED
Resume alloc_run_compile_expr_body_cases[builtin]:
  strip_tac >>
  Cases_on `l` >- (simp[alloc_run_def, compile_expr_body_def] >> gvs[alloc_run_def]) >>
  Cases_on `h` >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >> suspend "builtin_special"
QED
Resume alloc_run_compile_expr_body_cases[builtin_special]:
  Cases_on `t'` >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  Cases_on `h` >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  suspend "builtin_two_names"
QED
Resume alloc_run_compile_expr_body_cases[typebuiltin]:
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >> first_x_assum ACCEPT_TAC
QED
Resume alloc_run_compile_expr_body_cases[call]:
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >> first_x_assum ACCEPT_TAC
QED
Resume alloc_run_compile_expr_body_cases[pop]:
  simp[supported_expr_exists_def] >> strip_tac >>
  irule (Q.INST [`internal` |-> `F`] alloc_run_compile_expr_body_pop) >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED
Resume alloc_run_compile_expr_body_cases[builtin_two_names]:
  qmatch_asmsub_rename_tac `Name at a::Name bt bid::rest` >>
  Cases_on `rest`
  >- (Cases_on `b` >> simp[SF ETA_ss] >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      irule alloc_run_conseq >> irule_at Any alloc_run_compile_powmod256_names >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  Cases_on `h` >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >> suspend "builtin_three_names"
QED
Resume alloc_run_compile_expr_body_cases[builtin_three_names]:
  Cases_on `t'` >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  Cases_on `b` >> simp[SF ETA_ss] >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  irule alloc_run_conseq >>
  FIRST [irule_at Any alloc_run_compile_addmod_names,
         irule_at Any alloc_run_compile_mulmod_names] >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED
Finalise alloc_run_compile_expr_body_cases
