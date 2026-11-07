Theory bodyPtrStructLitOwnershipStmtLoops
Ancestors bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitCompilerOwnership compileEnv emitHelper stmtLowering
  loweringShapeDefs loweringShapeRules bodyPtrStructLitOwnershipShape
  bodyPtrStructLitLoopShapeEmit bodyPtrStructLitOwnershipControlFrame
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipInterfaces
  context exprLowering loweringShapeProps bodyPtrStructLitLoopShapeDynBody
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipReservation
  bodyPtrStructLitOwnershipEnvironment stackPlanTypes venomInst unitShapeDefs
  bodyPtrStructLitOwnershipStructFrame

Theorem alloc_run_emit_jmp_if_not_terminated:
  alloc_run (\s. T) (emit_jmp_if_not_terminated lbl) (\u s. T)
Proof
  rw[alloc_run_def, emit_jmp_if_not_terminated_def,
    comp_bind_def, comp_get_def] >>
  Cases_on `block_is_terminated s` >> gvs[comp_return_def, alloc_frame_refl] >>
  mp_tac (Q.INST [`opc` |-> `JMP`, `ops` |-> `[Label lbl]`, `outs` |-> `[]`]
    alloc_run_emit_inst) >> simp[alloc_run_def] >>
  disch_then drule >> simp[]
QED

Theorem alloc_run_emit_jmp_if_not_terminated_frame:
  shape_stable R /\ compiler_label lbl ==>
  alloc_run (\s. shape_state s /\ R s)
    (emit_jmp_if_not_terminated lbl) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any alloc_run_emit_jmp_if_not_terminated >> simp[] >>
  qexistsl [`F`, `\u s. R s`, `R`, `compiler_label`] >> simp[] >>
  simp[emit_jmp_if_not_terminated_def] >>
  irule shape_step_bind >> qexists `\cs s. R s` >> reverse conj_tac
  >- simp[shape_step_def, comp_get_def, shape_extends_refl] >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  simp[SF ETA_ss] >> irule (SRULE [SF ETA_ss] loop_shape_jmp) >> simp[]
QED

Theorem alloc_run_stmt_if_arm:
  shape_stable R /\ compiler_label lbl /\ compiler_label exit /\
  shape_step internal compiler_label R bfn (\u s. T) /\
  alloc_run (\s. shape_state s /\ R s) bfn (\u s. T) ==>
  alloc_run (\s. shape_state s /\ R s)
    (do new_block lbl; bfn; cs <- comp_get;
        emit_jmp_if_not_terminated exit;
        return (block_is_terminated cs) od)
    (\b s. shape_state s /\ R s)
Proof
  strip_tac >> simp[comp_ignore_bind_def, comp_bind_assoc] >>
  irule alloc_run_bind >> qexists `\u s. shape_state s /\ R s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block_frame >>
      qexists `R` >> simp[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
      qexistsl [`internal`, `R`, `\u s. T`, `R`, `compiler_label`, `\u s. T`] >>
      simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\cs s. shape_state s /\ R s` >> reverse conj_tac
  >- simp[alloc_run_def, comp_get_def, alloc_frame_refl] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s` >> reverse conj_tac
  >- simp[alloc_run_emit_jmp_if_not_terminated_frame] >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_if_tail:
  shape_stable R /\
  shape_step internal compiler_label R tfn (\u s. T) /\
  alloc_run (\s. shape_state s /\ R s) tfn (\u s. T) /\
  shape_step internal compiler_label R efn (\u s. T) /\
  alloc_run (\s. shape_state s /\ R s) efn (\u s. T) ==>
  alloc_run (\s. shape_state s /\ R s /\
      compiler_label th /\ compiler_label el /\ compiler_label exit)
    (do tb <- (do new_block th; tfn; cs <- comp_get;
                   emit_jmp_if_not_terminated exit;
                   return (block_is_terminated cs) od);
        eb <- (do new_block el; efn; cs <- comp_get;
                   emit_jmp_if_not_terminated exit;
                   return (block_is_terminated cs) od);
        if ~tb \/ ~eb then do new_block exit; return () od else return () od)
    (\u s. T)
Proof
  strip_tac >>
  reverse (Cases_on `compiler_label th`) >- simp[alloc_run_def] >>
  reverse (Cases_on `compiler_label el`) >- simp[alloc_run_def] >>
  reverse (Cases_on `compiler_label exit`) >- simp[alloc_run_def] >>
  simp[] >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ R s` >> reverse conj_tac
  >- (irule alloc_run_stmt_if_arm >> simp[] >> qexists `internal` >> simp[]) >>
  gen_tac >> BETA_TAC >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ R s` >> reverse conj_tac
  >- (irule alloc_run_stmt_if_arm >> simp[] >> qexists `internal` >> simp[]) >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- (simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
      qexists `\u s. T` >> reverse conj_tac
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block >> simp[]) >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_stmt_if:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce (BaseT BoolT) cond) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce (BaseT BoolT) cond) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_stmts ce lc ty ths) (\u s. T) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmts ce lc ty ths) (\u s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_stmts ce lc ty els) (\u s. T) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmts ce lc ty els) (\u s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lc ty (If cond ths els)) (\u s. T)
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\op s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `cond_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s cond_op) /\
    compiler_label l /\ label_sfx "then" l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s cond_op` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `th` >> simp[] >> suspend "labels"
QED

Resume alloc_run_compile_stmt_if[labels]:
  irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s cond_op /\
      compiler_label th /\ label_sfx "then" th) /\
    compiler_label l /\ label_sfx "else" l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\
        compiler_label th /\ label_sfx "then" th` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `el` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s cond_op /\
      compiler_label th /\ label_sfx "then" th /\
      compiler_label el /\ label_sfx "else" el) /\ compiler_label l` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s cond_op /\
        compiler_label th /\ label_sfx "then" th /\
        compiler_label el /\ label_sfx "else" el` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def,
        SRULE [] (Q.SPEC `[cond_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `exit` >> simp[] >> suspend "branches"
QED

Resume alloc_run_compile_stmt_if[branches]:
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ (cenv_shape_ok s ce /\
    compiler_label th /\ compiler_label el /\ compiler_label exit)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_jnz_frame >>
      qexists `\s. cenv_shape_ok s ce /\
        compiler_label th /\ compiler_label el /\ compiler_label exit` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def,
        plain_operand_def] >>
      metis_tac[SRULE [] (Q.INST [`s1` |-> `"then"`, `s2` |-> `"else"`] label_sfx_distinct)]) >>
  gen_tac >> simp[loop_comp_return_bind] >>
  simp[SF ETA_ss] >>
  ho_match_mp_tac (SRULE [comp_ignore_bind_def, comp_bind_assoc, loop_comp_return_bind, SF ETA_ss]
    alloc_run_stmt_if_tail) >>
  simp[cenv_shape_ok_stable] >> qexists `internal` >> simp[]
QED
Finalise alloc_run_compile_stmt_if

(* Shared by range and array iteration: explicit counter writes are legal
   only while the reserved register remains allocation-free. *)
Theorem alloc_run_stmt_loop_increment:
  alloc_run (\s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr)
    (do new_block incr;
        next <- emit_op ADD [Var ctr; Lit 1w];
        emit_inst ASSIGN [next] [ctr];
        emit_inst JMP [Label cond] [];
        new_block exit; return () od)
    (\u s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr)
Proof
  simp[comp_ignore_bind_def] >>
  ntac 2 (irule alloc_run_bind >>
    qexists `\v s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
    reverse conj_tac
    >- (ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac >- simp[alloc_run_assign_reserved] >> gen_tac >> simp[] >>
  ntac 2 (irule alloc_run_bind >>
    qexists `\v s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
    reverse conj_tac
    >- (ho_match_mp_tac alloc_run_frame_reserved >>
        simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_new_block_fresh,
          SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]) >>
    gen_tac >> simp[]) >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_loop_body_tail:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) bfn (\u s. T) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) bfn (\u s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ compiler_label incr /\
      not_fresh_at s ctr /\ ~alloc_owned s ctr)
    (do bfn; emit_jmp_if_not_terminated incr;
        new_block incr;
        next <- emit_op ADD [Var ctr; Lit 1w];
        emit_inst ASSIGN [next] [ctr];
        emit_inst JMP [Label cond] [];
        new_block exit; return () od)
    (\u s. T)
Proof
  strip_tac >> reverse (Cases_on `compiler_label incr`)
  >- simp[alloc_run_def] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ cenv_shape_ok s ce /\ compiler_label incr) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_shape_frame >>
      qexistsl [`ctr`, `internal`, `\s. cenv_shape_ok s ce /\ compiler_label incr`, `\u s. T`,
        `\s. cenv_shape_ok s ce`, `compiler_label`, `\u s. T`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_emit_jmp_if_not_terminated_frame >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ compiler_label incr`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_def] >>
      metis_tac[shape_base_fresh_outputs, shape_state_def]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_stmt_loop_increment) >> simp[]
QED

(* Public shape boundary for the reserved local commit.  Ownership must be
   measured from before declare_local, not from this instruction alone. *)
Theorem structlit_emit_local_alloca_shape:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (emit_local_alloca ce id) (\u s. cenv_shape_ok s ce)
Proof
  simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  rename1 `PtrVar op sz` >> Cases_on `op` >> simp[] >>
  TRY (irule shape_step_return >> simp[] >> NO_TAC) >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
  qexists `\s. cenv_shape_ok s ce` >>
  simp[cenv_shape_ok_stable, label_or_plain_def, plain_operand_def,
    is_label_operand_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_terminator_def, is_read0_opcode_def, label_positions_ok_def,
    operand_case_not_label, is_param_opcode_def] >>
  qexists `compiler_label` >> simp[] >>
  rw[cenv_shape_ok_def] >>
  first_x_assum (drule_at Any) >> simp[loc_shape_ok_def, plain_operand_def]
QED

Theorem alloc_run_declare_local_commit:
  ce.ce_alloca_locals /\ shape_stable R ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ R s)
    (do env <- declare_local ce id ty;
        emit_local_alloca env id; return env od)
    (\env s. shape_state s /\ cenv_shape_ok s env /\
      env.ce_return_pc = ce.ce_return_pc /\ env.ce_alloca_locals /\ R s)
Proof
  strip_tac >> simp[alloc_run_def, comp_ignore_bind_def, comp_bind_def,
    comp_return_def] >> rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `shape_base_state s` by gvs[shape_state_def] >>
  drule_all declare_local_alloca_fresh_commit >> strip_tac >>
  drule declare_local_alloca_mode >> strip_tac >> simp[] >>
  `shape_state cs' /\ cenv_shape_ok cs' env /\
    shape_extends F compiler_label s cs' /\
    env.ce_return_pc = ce.ce_return_pc` by
    (mp_tac (Q.SPEC `F` declare_local_shape) >>
     simp[shape_step_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`internal` |-> `F`, `ce` |-> `env`]
    structlit_emit_local_alloca_shape) >>
  simp[shape_step_def] >> metis_tac[shape_stable_def]
QED

Theorem alloc_run_stmt_range_inputs:
  ce.ce_alloca_locals /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce fty start_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce fty start_e) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce fty end_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce fty end_e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (do start_op <- lower_value compile_expr ce fty start_e;
        end_op <- lower_value compile_expr ce fty end_e;
        env <- declare_local ce id fty;
        emit_local_alloca env id; return (start_op,end_op,env) od)
    (\(start_op,end_op,env) s.
      shape_state s /\ cenv_shape_ok s env /\ env.ce_alloca_locals /\
      env.ce_return_pc = ce.ce_return_pc /\
      plain_operand s start_op /\ plain_operand s end_op)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\op s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `start_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\op s. shape_state s /\ cenv_shape_ok s ce /\
    plain_operand s start_op /\ plain_operand s op` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. plain_operand s start_op`] >>
      simp[SRULE [] (Q.SPEC `[start_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `end_op` >> simp[] >>
  `alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\
      (plain_operand s start_op /\ plain_operand s end_op))
    (do env <- declare_local ce id fty;
        emit_local_alloca env id; return env od)
    (\env s. shape_state s /\ cenv_shape_ok s env /\
      env.ce_return_pc = ce.ce_return_pc /\ env.ce_alloca_locals /\
      (plain_operand s start_op /\ plain_operand s end_op))` by
    (ho_match_mp_tac alloc_run_declare_local_commit >>
     simp[shape_stable_conj,
       SRULE [] (Q.SPEC `[start_op;end_op]` shape_stable_plain_operands)]) >>
  simp[alloc_run_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `declare_local ce id fty s` >> gvs[] >>
  rename1 `declare_local ce id fty s = (env0,st0)` >>
  Cases_on `emit_local_alloca env0 id st0` >> gvs[] >>
  qpat_x_assum `alloc_run _ _ _` mp_tac >>
  simp[alloc_run_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  disch_then drule >> simp[]
QED

Theorem structlit_range_bound_checks_shape:
  shape_step F compiler_label
    (\s. plain_operand s start_op /\ plain_operand s end_op /\ plain_operand s rounds)
    (compile_range_bound_checks start_op end_op rounds bound signed) (\u s. T)
Proof
  simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  irule shape_step_bind >>
  qexists `\v s. plain_operand s v /\ plain_operand s rounds` >> reverse conj_tac
  >- (Cases_on `signed` >> simp[] >> irule shape_step_conseq >>
      irule_at Any loop_shape_op >>
      qexists `\s. plain_operand s start_op /\ plain_operand s end_op /\ plain_operand s rounds` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[start_op;end_op;rounds]` shape_stable_plain_operands),
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def] >>
      gvs[plain_operand_def, is_label_operand_def, operand_case_not_label]) >>
  qx_gen_tac `bad_order` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\v s. plain_operand s v /\ plain_operand s rounds` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_op >>
      qexists `\s. plain_operand s bad_order /\ plain_operand s rounds` >>
      simp[SRULE [] (Q.SPEC `[bad_order;rounds]` shape_stable_plain_operands)] >>
      rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `good_order` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\u s. plain_operand s rounds` >> reverse conj_tac
  >- suspend "assert_order" >>
  gen_tac >> BETA_TAC >> suspend "rounds"
QED

Resume structlit_range_bound_checks_shape[assert_order]:
  irule shape_step_conseq >> irule_at Any loop_shape_void >>
  qexists `\s. plain_operand s good_order /\ plain_operand s rounds` >>
  simp[SRULE [] (Q.SPEC `[good_order;rounds]` shape_stable_plain_operands),
    lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def] >>
  gvs[plain_operand_def, is_label_operand_def, operand_case_not_label]
QED

Resume structlit_range_bound_checks_shape[rounds]:
  irule shape_step_bind >> qexists `\v s. plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_op >>
      qexists `\s. plain_operand s rounds` >>
      simp[SRULE [] (Q.SPEC `[rounds]` shape_stable_plain_operands), plain_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, is_label_operand_def, operand_case_not_label]) >>
  qx_gen_tac `bad_rounds` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\v s. plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_op >>
      qexists `\s. plain_operand s bad_rounds` >>
      simp[SRULE [] (Q.SPEC `[bad_rounds]` shape_stable_plain_operands)] >>
      rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `good_rounds` >> BETA_TAC >>
  irule shape_step_conseq >> irule_at Any loop_shape_void >>
  qexists `\s. plain_operand s good_rounds` >>
  simp[SRULE [] (Q.SPEC `[good_rounds]` shape_stable_plain_operands),
    lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def] >>
  gvs[plain_operand_def, is_label_operand_def, operand_case_not_label]
QED
Finalise structlit_range_bound_checks_shape

Theorem structlit_range_rounds_shape:
  shape_step F compiler_label
    (\s. plain_operand s end_op /\ plain_operand s start_op)
    (case (e1,e2) of
       (Literal _ (IntL n1),Literal _ (IntL n2)) =>
         comp_return (Lit (i2w n2 - i2w n1))
     | _ => emit_op SUB [end_op;start_op]) (\r s. plain_operand s r)
Proof
  `shape_step F compiler_label
    (\s. plain_operand s end_op /\ plain_operand s start_op)
    (emit_op SUB [end_op;start_op]) (\r s. plain_operand s r)` by
    (irule shape_step_conseq >> irule_at Any loop_shape_op >>
     qexists `\s. plain_operand s end_op /\ plain_operand s start_op` >>
     simp[SRULE [] (Q.SPEC `[end_op;start_op]` shape_stable_plain_operands),
       plain_operand_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
       is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
       is_label_operand_def, operand_case_not_label]) >>
  `!w. shape_step F compiler_label
    (\s. plain_operand s end_op /\ plain_operand s start_op)
    (comp_return (Lit w)) (\r s. plain_operand s r)` by
    (gen_tac >> irule shape_step_return >>
     simp[plain_operand_def, is_label_operand_def]) >>
  Cases_on `e1` >> Cases_on `e2` >> simp[] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem alloc_run_stmt_range_rounds:
  alloc_run fresh_outputs
    (case (e1,e2) of
       (Literal _ (IntL n1),Literal _ (IntL n2)) =>
         comp_return (Lit (i2w n2 - i2w n1))
     | _ => emit_op SUB [end_op;start_op]) (\r s. fresh_outputs s)
Proof
  `!w. alloc_run fresh_outputs (comp_return (Lit w)) (\r s. fresh_outputs s)` by
    simp[alloc_run_def, comp_return_def, alloc_frame_refl] >>
  gvs[SF ETA_ss] >> Cases_on `e1` >> Cases_on `e2` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem structlit_range_checks_shape:
  shape_step F compiler_label
    (\s. plain_operand s start_op /\ plain_operand s end_op /\ plain_operand s rounds)
    (case (e1,e2) of
       (Literal _ (IntL _),Literal _ (IntL _)) => comp_return ()
     | _ => compile_range_bound_checks start_op end_op rounds bound signed)
    (\u s. T)
Proof
  `shape_step F compiler_label
    (\s. plain_operand s start_op /\ plain_operand s end_op /\ plain_operand s rounds)
    (comp_return ()) (\u s. T)` by (irule shape_step_return >> simp[]) >>
  Cases_on `e1` >> Cases_on `e2` >> simp[structlit_range_bound_checks_shape] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[structlit_range_bound_checks_shape]
QED

Theorem alloc_run_stmt_range_checks:
  alloc_run fresh_outputs
    (case (e1,e2) of
       (Literal _ (IntL _),Literal _ (IntL _)) => comp_return ()
     | _ => compile_range_bound_checks start_op end_op rounds bound signed)
    (\u s. fresh_outputs s)
Proof
  `alloc_run fresh_outputs (comp_return ()) (\u s. fresh_outputs s)` by
    simp[alloc_run_def, comp_return_def, alloc_frame_refl] >>
  gvs[SF ETA_ss] >> Cases_on `e1` >> Cases_on `e2` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_range_bound_checks] >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_range_bound_checks]
QED

Theorem alloc_run_stmt_range_trip_count:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s start_op /\ plain_operand s end_op)
    (do rounds <-
          (case (e1,e2) of
             (Literal _ (IntL n1),Literal _ (IntL n2)) =>
               comp_return (Lit (i2w n2 - i2w n1))
           | _ => emit_op SUB [end_op;start_op]);
        (case (e1,e2) of
           (Literal _ (IntL _),Literal _ (IntL _)) => comp_return ()
         | _ => compile_range_bound_checks start_op end_op rounds bound signed);
        emit_op ADD [start_op;rounds] od)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\r s. shape_state s /\
    (R s /\ plain_operand s start_op /\ plain_operand s end_op) /\ plain_operand s r` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any (SRULE [] structlit_range_rounds_shape) >>
      qexists `\s. R s /\ plain_operand s start_op /\ plain_operand s end_op` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[start_op;end_op]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_stmt_range_rounds]) >>
  qx_gen_tac `rounds` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ plain_operand s start_op /\ plain_operand s rounds` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any (SRULE [] structlit_range_checks_shape) >>
      qexists `\s. R s /\ plain_operand s start_op /\ plain_operand s rounds` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[start_op;rounds]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_stmt_range_checks]) >>
  gen_tac >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
  irule_at Any loop_shape_op >> qexists `R` >>
  qexists `\s. plain_operand s start_op /\ plain_operand s rounds` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[start_op;rounds]` shape_stable_plain_operands),
    alloc_run_emit_op_fresh, plain_operand_def,
    lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def, is_label_operand_def, operand_case_not_label]
QED

Theorem alloc_run_stmt_loop_counter:
  shape_stable R /\ compiler_label entry ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s init)
    (do emit_inst JMP [Label entry] []; new_block entry;
        ctr <- fresh_var; emit_inst ASSIGN [init] [ctr]; return ctr od)
    (\ctr s. shape_state s /\ R s /\ plain_operand s (Var ctr) /\
      not_fresh_at s ctr /\ ~alloc_owned s ctr)
Proof
  strip_tac >> Cases_on `is_label_operand init`
  >- simp[alloc_run_def, plain_operand_def] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ (R s /\ plain_operand s init)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any loop_shape_jmp >>
      qexistsl [`\s. R s /\ plain_operand s init`, `\s. T`] >>
      simp[shape_stable_conj, shape_stable_def,
        SRULE [] (Q.SPEC `[init]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ (R s /\ plain_operand s init)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block_frame >>
      qexists `\s. R s /\ plain_operand s init` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[init]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\ctr s. shape_state s /\ (R s /\ plain_operand s init) /\
    plain_operand s (Var ctr) /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_var_frame >>
      qexists `\s. R s /\ plain_operand s init` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[init]` shape_stable_plain_operands)]) >>
  qx_gen_tac `ctr` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ plain_operand s (Var ctr) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- suspend "assign" >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Resume alloc_run_stmt_loop_counter[assign]:
  irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
  irule_at Any alloc_run_emit_inst_frame >>
  qexistsl [`ctr`, `F`, `\s. R s /\ plain_operand s (Var ctr)`] >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[Var ctr]` shape_stable_plain_operands),
    label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, is_label_operand_def, operand_case_not_label]
QED
Finalise alloc_run_stmt_loop_counter

Theorem alloc_run_stmt_loop_test:
  shape_stable R /\ compiler_label cond /\ compiler_label exit /\
  compiler_label body_lbl /\ exit <> body_lbl ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s (Var ctr) /\ plain_operand s limit)
    (do emit_inst JMP [Label cond] []; new_block cond;
        done_op <- emit_op EQ [Var ctr;limit];
        emit_inst JNZ [done_op;Label exit;Label body_lbl] [];
        new_block body_lbl od)
    (\u s. shape_state s /\ R s)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\
    (R s /\ plain_operand s (Var ctr) /\ plain_operand s limit)` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_jmp_frame >>
      qexists `\s. R s /\ plain_operand s (Var ctr) /\ plain_operand s limit` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var ctr;limit]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\
    (R s /\ plain_operand s (Var ctr) /\ plain_operand s limit)` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_new_block_frame >>
      qexists `\s. R s /\ plain_operand s (Var ctr) /\ plain_operand s limit` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[Var ctr;limit]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any loop_shape_op >>
      qexistsl [`R`, `\s. plain_operand s (Var ctr) /\ plain_operand s limit`] >>
      simp[SRULE [] (Q.SPEC `[Var ctr;limit]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_jnz_frame >>
      qexists `R` >> simp[plain_operand_def]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_new_block_frame >> qexists `R` >> simp[]
QED

Theorem structlit_range_store_shape:
  shape_step F compiler_label
    (\s. cenv_shape_ok s ce /\ plain_operand s (Var ctr))
    (case FLOOKUP ce.ce_vars id of
       SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off);Var ctr]
     | SOME (PtrVar ptr_op _) => emit_void MSTORE [ptr_op;Var ctr]
     | _ => emit_void INVALID []) (\u s. T)
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- (irule shape_step_conseq >> irule_at Any loop_shape_void >>
      qexists `\s. T` >> simp[shape_stable_def, lowered_inst_ok_def,
        mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  irule shape_step_conseq >> irule_at Any loop_shape_void >>
  qexists `\s. cenv_shape_ok s ce /\ plain_operand s (Var ctr)` >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[Var ctr]` shape_stable_plain_operands),
    lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def, plain_operand_def,
    is_label_operand_def, operand_case_not_label] >>
  rw[cenv_shape_ok_def] >>
  first_x_assum (drule_at Any) >> simp[loc_shape_ok_def, plain_operand_def] >>
  strip_tac >> simp[is_label_operand_def] >> Cases_on `o'` >>
  gvs[plain_operand_def, is_label_operand_def, operand_case_not_label]
QED

Theorem alloc_run_stmt_range_store:
  alloc_run fresh_outputs
    (case FLOOKUP ce.ce_vars id of
       SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off);Var ctr]
     | SOME (PtrVar ptr_op _) => emit_void MSTORE [ptr_op;Var ctr]
     | _ => emit_void INVALID []) (\u s. fresh_outputs s)
Proof
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED
