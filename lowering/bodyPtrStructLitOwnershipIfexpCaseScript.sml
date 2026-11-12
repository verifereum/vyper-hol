Theory bodyPtrStructLitOwnershipIfexpCase
Ancestors bodyPtrStructLitOwnershipControlFrame bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFrame
  bodyPtrStructLitOwnershipMemory loweringShapeProps loweringShapeDefs loweringShapeRules
  exprLowering compileEnv context venomInst stackPlanTypes

Theorem alloc_run_compile_expr_body_ifexp:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (BaseT BoolT) cond) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (BaseT BoolT) cond) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty th) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty th) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty el) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty el) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (IfExp a cond th el)) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `cond_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\x s. shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s cond_op) /\
    plain_operand s (Var x) /\ not_fresh_at s x /\ ~alloc_owned s x` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. cenv_shape_ok s ce /\ plain_operand s cond_op`]
        alloc_run_fresh_var_frame) >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)] >>
      qexistsl [`cond_op`, `ce`] >> simp[]) >>
  qx_gen_tac `result_var` >> simp[] >> suspend "labels"
QED

Resume alloc_run_compile_expr_body_ifexp[labels]:
  irule alloc_run_bind >>
  qexists `\l s. (shape_state s /\
    (cenv_shape_ok s ce /\ plain_operand s cond_op /\ plain_operand s (Var result_var)) /\
    compiler_label l /\ label_sfx "then" l) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_label_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\ plain_operand s (Var result_var)`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands)]) >>
  qx_gen_tac `then_lbl` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. (shape_state s /\
    (cenv_shape_ok s ce /\ plain_operand s cond_op /\ plain_operand s (Var result_var) /\
     compiler_label then_lbl /\ label_sfx "then" then_lbl) /\
    compiler_label l /\ label_sfx "else" l) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_label_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\
        plain_operand s (Var result_var) /\ compiler_label then_lbl /\ label_sfx "then" then_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `else_lbl` >> simp[] >> suspend "exit_label"
QED

Resume alloc_run_compile_expr_body_ifexp[exit_label]:
  irule alloc_run_bind >>
  qexists `\l s. (shape_state s /\
    (cenv_shape_ok s ce /\ plain_operand s cond_op /\ plain_operand s (Var result_var) /\
     compiler_label then_lbl /\ label_sfx "then" then_lbl /\
     compiler_label else_lbl /\ label_sfx "else" else_lbl) /\ compiler_label l) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_label_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\
        plain_operand s (Var result_var) /\ compiler_label then_lbl /\ label_sfx "then" then_lbl /\
        compiler_label else_lbl /\ label_sfx "else" else_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `exit_lbl` >> simp[] >> suspend "branch"
QED

Resume alloc_run_compile_expr_body_ifexp[branch]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
    compiler_label then_lbl /\ compiler_label else_lbl /\ compiler_label exit_lbl)) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_jnz_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
        compiler_label then_lbl /\ compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def,
        plain_operand_def] >>
      metis_tac[SRULE [] (Q.INST [`s1` |-> `"then"`, `s2` |-> `"else"`] label_sfx_distinct)]) >>
  gen_tac >> simp[] >> suspend "then_block"
QED

Resume alloc_run_compile_expr_body_ifexp[then_block]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
    compiler_label else_lbl /\ compiler_label exit_lbl)) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_new_block_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
        compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\vv s. (shape_state s /\
    (plain_operand s (Var result_var) /\ compiler_label else_lbl /\ compiler_label exit_lbl) /\
    cenv_shape_ok s ce /\ value_shape_ok s vv) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`result_var`, `internal`, `ce`, `\s. plain_operand s (Var result_var) /\
        compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `then_vv` >> simp[] >> suspend "then_convert"
QED

Resume alloc_run_compile_expr_body_ifexp[then_convert]:
  irule alloc_run_bind >>
  qexists `\op s. (shape_state s /\
    (plain_operand s (Var result_var) /\ compiler_label else_lbl /\ compiler_label exit_lbl) /\
    cenv_shape_ok s ce /\ plain_operand s op) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_compile_ifexp_arm_frame >>
      qexistsl [`result_var`, `\s. plain_operand s (Var result_var) /\
        compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `then_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\
    (cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
      compiler_label else_lbl /\ compiler_label exit_lbl)) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_assign_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
        compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  gen_tac >> simp[] >> suspend "then_jump"
QED

Resume alloc_run_compile_expr_body_ifexp[then_jump]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
    compiler_label else_lbl /\ compiler_label exit_lbl)) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_jmp_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
        compiler_label else_lbl /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
    compiler_label exit_lbl)) /\ not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_new_block_frame >>
      qexistsl [`result_var`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var result_var) /\
        compiler_label exit_lbl`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  gen_tac >> simp[] >> suspend "else_call"
QED

Resume alloc_run_compile_expr_body_ifexp[else_call]:
  irule alloc_run_bind >>
  qexists `\vv s. (shape_state s /\
    (plain_operand s (Var result_var) /\ compiler_label exit_lbl) /\
    cenv_shape_ok s ce /\ value_shape_ok s vv) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`result_var`, `internal`, `ce`, `\s. plain_operand s (Var result_var) /\
        compiler_label exit_lbl`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `else_vv` >> simp[] >> irule alloc_run_bind >>
  qexists `\op s. (shape_state s /\
    (plain_operand s (Var result_var) /\ compiler_label exit_lbl) /\
    cenv_shape_ok s ce /\ plain_operand s op) /\
    not_fresh_at s result_var /\ ~alloc_owned s result_var` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_compile_ifexp_arm_frame >>
      qexistsl [`result_var`, `\s. plain_operand s (Var result_var) /\ compiler_label exit_lbl`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var result_var]` shape_stable_plain_operands), shape_stable_def]) >>
  qx_gen_tac `else_op` >> simp[] >> suspend "else_assign"
QED

Resume alloc_run_compile_expr_body_ifexp[else_assign]:
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ compiler_label exit_lbl` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_assign_frame >>
      qexists `\s. compiler_label exit_lbl` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ compiler_label exit_lbl` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_jmp_frame >>
      qexists `\s. compiler_label exit_lbl` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ T` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block_frame >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> Cases_on `is_word_type (expr_type (IfExp a cond th el))` >>
  simp[] >> irule alloc_run_return >> simp[]
QED

Finalise alloc_run_compile_expr_body_ifexp
