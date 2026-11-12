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
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitCreationShape

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

Theorem alloc_run_stmt_range_after_labels:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_stmts ce (InLoop exit incr) ty stmts) (\u s. T) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmts ce (InLoop exit incr) ty stmts) (\u s. T) /\
  compiler_label entry /\ compiler_label cond /\ compiler_label body_lbl /\
  compiler_label incr /\ compiler_label exit /\ exit <> body_lbl ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\
      plain_operand s start_op /\ plain_operand s end_op)
    (do ctr <- (do emit_inst JMP [Label entry] []; new_block entry;
                   ctr <- fresh_var; emit_inst ASSIGN [start_op] [ctr]; return ctr od);
        limit <- (do rounds <-
          (case (e1,e2) of
             (Literal _ (IntL n1),Literal _ (IntL n2)) =>
               comp_return (Lit (i2w n2 - i2w n1))
           | _ => emit_op SUB [end_op;start_op]);
          (case (e1,e2) of
             (Literal _ (IntL _),Literal _ (IntL _)) => comp_return ()
           | _ => compile_range_bound_checks start_op end_op rounds bound signed);
          emit_op ADD [start_op;rounds] od);
        (do emit_inst JMP [Label cond] []; new_block cond;
            done_op <- emit_op EQ [Var ctr;limit];
            emit_inst JNZ [done_op;Label exit;Label body_lbl] [];
            new_block body_lbl od);
        (case FLOOKUP ce.ce_vars id of
           SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off);Var ctr]
         | SOME (PtrVar ptr_op _) => emit_void MSTORE [ptr_op;Var ctr]
         | _ => emit_void INVALID []);
        compile_stmts ce (InLoop exit incr) ty stmts;
        emit_jmp_if_not_terminated incr;
        new_block incr; next <- emit_op ADD [Var ctr;Lit 1w];
        emit_inst ASSIGN [next] [ctr]; emit_inst JMP [Label cond] [];
        new_block exit; return () od) (\u s. T)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\ctr s. shape_state s /\
    (cenv_shape_ok s ce /\ plain_operand s start_op /\ plain_operand s end_op) /\
    plain_operand s (Var ctr) /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_loop_counter >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s start_op /\ plain_operand s end_op` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[start_op;end_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `ctr` >> simp[] >> suspend "trip"
QED

Resume alloc_run_stmt_range_after_labels[trip]:
  irule alloc_run_bind >>
  qexists `\v s. (shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s (Var ctr)) /\
      plain_operand s v) /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any (SRULE [] alloc_run_stmt_range_trip_count) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var ctr)`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var ctr]` shape_stable_plain_operands)]) >>
  qx_gen_tac `limit` >> simp[] >> suspend "test"
QED

Resume alloc_run_stmt_range_after_labels[test]:
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ cenv_shape_ok s ce /\ plain_operand s (Var ctr)) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_stmt_loop_test) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ plain_operand s (Var ctr)`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[Var ctr]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> suspend "store"
QED
Resume alloc_run_stmt_range_after_labels[store]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ cenv_shape_ok s ce) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any (SRULE [] structlit_range_store_shape) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce`] >>
      simp[cenv_shape_ok_stable, SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_stmt_range_store]) >>
  gen_tac >> simp[] >>
  irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_stmt_loop_body_tail) >>
  simp[] >> qexistsl [`internal`, `ce`] >> simp[]
QED
Finalise alloc_run_stmt_range_after_labels

Theorem alloc_run_stmt_loop_labels:
  shape_stable R /\ exit_sfx <> body_sfx /\
  (!entry cond body_lbl incr exit.
    compiler_label entry /\ compiler_label cond /\ compiler_label body_lbl /\
    compiler_label incr /\ compiler_label exit /\ exit <> body_lbl ==>
    alloc_run (\s. shape_state s /\ R s)
      (f entry cond body_lbl incr exit) (\u s. T)) ==>
  alloc_run (\s. shape_state s /\ R s)
    (do entry <- fresh_label entry_sfx;
        cond <- fresh_label cond_sfx;
        body_lbl <- fresh_label body_sfx;
        incr <- fresh_label incr_sfx;
        exit <- fresh_label exit_sfx;
        f entry cond body_lbl incr exit od) (\u s. T)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ R s /\ compiler_label l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `R` >> simp[]) >>
  qx_gen_tac `entry` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (R s /\ compiler_label entry) /\ compiler_label l` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. R s /\ compiler_label entry` >>
      simp[shape_stable_def] >> metis_tac[shape_stable_def]) >>
  qx_gen_tac `cond` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (R s /\ compiler_label entry /\ compiler_label cond) /\
    compiler_label l /\ label_sfx body_sfx l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. R s /\ compiler_label entry /\ compiler_label cond` >>
      simp[shape_stable_def] >> metis_tac[shape_stable_def]) >>
  qx_gen_tac `body_lbl` >> simp[] >> suspend "last_labels"
QED

Resume alloc_run_stmt_loop_labels[last_labels]:
  irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (R s /\ compiler_label entry /\ compiler_label cond /\
    compiler_label body_lbl /\ label_sfx body_sfx body_lbl) /\ compiler_label l` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. R s /\ compiler_label entry /\ compiler_label cond /\
        compiler_label body_lbl /\ label_sfx body_sfx body_lbl` >>
      simp[shape_stable_def] >> metis_tac[shape_stable_def]) >>
  qx_gen_tac `incr` >> simp[] >> irule alloc_run_bind >>
  qexists `\l s. shape_state s /\ (R s /\ compiler_label entry /\ compiler_label cond /\
    compiler_label body_lbl /\ label_sfx body_sfx body_lbl /\ compiler_label incr) /\
    compiler_label l /\ label_sfx exit_sfx l` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. R s /\ compiler_label entry /\ compiler_label cond /\
        compiler_label body_lbl /\ label_sfx body_sfx body_lbl /\ compiler_label incr` >>
      simp[shape_stable_def] >> metis_tac[shape_stable_def]) >>
  qx_gen_tac `exit` >> fs[alloc_run_def] >> rpt strip_tac >>
  `exit <> body_lbl` by
    (irule label_sfx_distinct >> qexistsl [`exit_sfx`, `body_sfx`] >> simp[]) >>
  first_x_assum (drule_at (Pat `f _ _ _ _ _ _ = _`)) >> simp[]
QED
Finalise alloc_run_stmt_loop_labels

Theorem alloc_run_declare_local_commit_then:
  ce.ce_alloca_locals /\ shape_stable R /\
  (!env. env.ce_alloca_locals /\ env.ce_return_pc = ce.ce_return_pc ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s env /\ R s) (k env) Q) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ R s)
    (do env <- declare_local ce id fty; emit_local_alloca env id; k env od) Q
Proof
  strip_tac >>
  `alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ R s)
    (comp_bind (do env <- declare_local ce id fty;
                   emit_local_alloca env id; return env od) k) Q` suffices_by
    simp[comp_ignore_bind_def, comp_bind_assoc, loop_comp_return_bind] >>
  irule alloc_run_bind >>
  qexists `\env s. shape_state s /\ cenv_shape_ok s env /\
    env.ce_return_pc = ce.ce_return_pc /\ env.ce_alloca_locals /\ R s` >>
  reverse conj_tac >- simp[alloc_run_declare_local_commit] >>
  gen_tac >> fs[alloc_run_def] >> rpt strip_tac >>
  first_x_assum (drule_at (Pat `k _ _ = _`)) >> simp[]
QED

Theorem alloc_run_compile_stmt_range:
  ce.ce_alloca_locals /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce fty start_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce fty start_e) (\v s. T) /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce fty end_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce fty end_e) (\v s. T) /\
  (!env exit incr. env.ce_alloca_locals /\ env.ce_return_pc = ce.ce_return_pc /\
    compiler_label exit /\ compiler_label incr ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s env)
      (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
      (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound stmts)) (\u s. T)
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
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
  qx_gen_tac `end_op` >> simp[] >> suspend "commit"
QED

Resume alloc_run_compile_stmt_range[commit]:
  ho_match_mp_tac (SRULE [comp_ignore_bind_def] alloc_run_declare_local_commit_then) >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[start_op;end_op]` shape_stable_plain_operands)] >>
  qx_gen_tac `env` >> strip_tac >> suspend "labels"
QED

Resume alloc_run_compile_stmt_range[labels]:
  ho_match_mp_tac alloc_run_stmt_loop_labels >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[start_op;end_op]` shape_stable_plain_operands)] >>
  rpt gen_tac >> strip_tac >>
  irule (SRULE [comp_ignore_bind_def, comp_bind_assoc, loop_comp_return_bind]
    alloc_run_stmt_range_after_labels) >> simp[] >>
  qexists `internal` >>
  first_x_assum (drule_at (Pat `_.ce_alloca_locals`)) >> simp[]
QED
Finalise alloc_run_compile_stmt_range

Theorem alloc_run_stmt_array_length:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ R s /\ plain_operand s arr_op)
    (if dynamic then compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc arr_op
     else comp_return (Lit (n2w capacity)))
    (\v s. shape_state s /\ cenv_shape_ok s ce /\ R s /\
      plain_operand s arr_op /\ plain_operand s v)
Proof
  strip_tac >> Cases_on `dynamic` >> simp[]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any compile_ptr_load_cenv_shape >>
      qexists `\s. cenv_shape_ok s ce /\ R s /\ plain_operand s arr_op` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[arr_op]` shape_stable_plain_operands),
        alloc_run_compile_ptr_load]) >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl,
    plain_operand_def, is_label_operand_def]
QED

Theorem structlit_array_capacity_check_shape:
  shape_step F compiler_label (\s. plain_operand s len)
    (if dynamic then
       do invalid <- emit_op GT [len;Lit (n2w capacity)];
          valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
     else comp_return ()) (\u s. T)
Proof
  Cases_on `dynamic` >> simp[]
  >- (irule shape_step_bind >> qexists `\v s. plain_operand s v` >> reverse conj_tac
      >- (irule shape_step_conseq >> irule_at Any loop_shape_op >>
          qexists `\s. plain_operand s len` >>
          simp[SRULE [] (Q.SPEC `[len]` shape_stable_plain_operands),
            lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
            inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
            label_positions_ok_def, is_terminator_def, plain_operand_def,
            is_label_operand_def, operand_case_not_label]) >>
      qx_gen_tac `invalid` >> BETA_TAC >> irule shape_step_bind >>
      qexists `\v s. plain_operand s v` >> reverse conj_tac
      >- (irule shape_step_conseq >> irule_at Any loop_shape_op >>
          qexists `\s. plain_operand s invalid` >>
          simp[SRULE [] (Q.SPEC `[invalid]` shape_stable_plain_operands)] >>
          rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
          simp[] >> qexists `s` >> simp[]) >>
      qx_gen_tac `valid` >> BETA_TAC >>
      irule shape_step_conseq >> irule_at Any loop_shape_void >>
      qexists `\s. plain_operand s valid` >>
      simp[SRULE [] (Q.SPEC `[valid]` shape_stable_plain_operands),
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, plain_operand_def,
        is_label_operand_def, operand_case_not_label]) >>
  irule shape_step_return >> simp[]
QED

Theorem alloc_run_stmt_array_capacity_check:
  alloc_run fresh_outputs
    (if dynamic then
       do invalid <- emit_op GT [len;Lit (n2w capacity)];
          valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
     else comp_return ()) (\u s. fresh_outputs s)
Proof
  Cases_on `dynamic` >> simp[]
  >- (ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
        reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
        gen_tac >> simp[]) >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem structlit_array_element_offset_shape:
  shape_step F compiler_label (\s. plain_operand s idx_offset)
    (if 0 < offset_base then emit_op ADD [Lit (n2w offset_base);idx_offset]
     else comp_return idx_offset) (\v s. plain_operand s v)
Proof
  Cases_on `0 < offset_base` >> simp[]
  >- (irule shape_step_emit_op_pre >>
      simp[label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, is_label_operand_def, operand_case_not_label]) >>
  irule shape_step_return >> simp[]
QED

Theorem alloc_run_stmt_array_element_offset:
  alloc_run fresh_outputs
    (if 0 < offset_base then emit_op ADD [Lit (n2w offset_base);idx_offset]
     else comp_return idx_offset) (\v s. fresh_outputs s)
Proof
  Cases_on `0 < offset_base` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_array_element_address:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s (Var ctr) /\ plain_operand s arr_op)
    (do idx_offset <- emit_op MUL [Var ctr;Lit (n2w elem_size)];
        total_offset <-
          (if 0 < offset_base then emit_op ADD [Lit (n2w offset_base);idx_offset]
           else comp_return idx_offset);
        emit_op ADD [arr_op;total_offset] od)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (R s /\ plain_operand s arr_op) /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any loop_shape_op >>
      qexistsl [`\s. R s /\ plain_operand s arr_op`, `\s. plain_operand s (Var ctr)`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[arr_op]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, is_label_operand_def, operand_case_not_label]) >>
  qx_gen_tac `idx_offset` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (R s /\ plain_operand s arr_op) /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any structlit_array_element_offset_shape >>
      qexists `\s. R s /\ plain_operand s arr_op` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[arr_op]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [SF ETA_ss] alloc_run_stmt_array_element_offset]) >>
  qx_gen_tac `total_offset` >> simp[] >> suspend "address"
QED

Resume alloc_run_stmt_array_element_address[address]:
  irule alloc_run_conseq >> irule_at Any alloc_run_fresh_shape_frame >>
  irule_at Any loop_shape_op >> qexistsl [`R`,
    `\s. plain_operand s arr_op /\ plain_operand s total_offset`] >>
  simp[SRULE [] (Q.SPEC `[arr_op;total_offset]` shape_stable_plain_operands),
    SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, is_label_operand_def, operand_case_not_label]
QED
Finalise alloc_run_stmt_array_element_address

Theorem structlit_iter_load_store_shape[local]:
  shape_step F compiler_label
    (\s. cenv_shape_ok s ce /\ plain_operand s src /\ plain_operand s dst)
    (do v <- compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc src;
        emit_void MSTORE [dst;v] od) (\u s. T)
Proof
  irule shape_step_bind >>
  qexists `\v s. plain_operand s dst /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any compile_ptr_load_cenv_shape >>
      qexists `\s. plain_operand s dst` >>
      simp[SRULE [] (Q.SPEC `[dst]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> irule shape_step_emit_void_pre >>
  simp[label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, is_label_operand_def, operand_case_not_label]
QED

Theorem structlit_iter_elem_copy_shape:
  shape_step F compiler_label
    (\s. cenv_shape_ok s ce /\ plain_operand s src /\ plain_operand s dst)
    (compile_iter_elem_copy ce src dst elem_size loc (is_slot_addressed loc) target_ty elem_ty)
    (\u s. T)
Proof
  Cases_on `is_slot_addressed loc`
  >- (simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >> irule shape_step_bind >>
      qexists `\u s. T` >> conj_tac
      >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
      irule shape_step_conseq >> irule_at Any create_slot_to_memory_shape >>
      Cases_on `loc` >> gvs[is_slot_addressed_def]) >>
  simp[compile_iter_elem_copy_def] >> Cases_on `loc <> LocMemory` >> simp[]
  >- (Cases_on `elem_size <= 32` >> simp[structlit_iter_load_store_shape] >>
      Cases_on `loc` >> gvs[is_slot_addressed_def] >> suspend "bulk") >>
  gvs[] >> Cases_on `is_word_type target_ty` >> simp[]
  >- (mp_tac (Q.INST [`loc` |-> `LocMemory`] structlit_iter_load_store_shape) >>
      simp[compile_ptr_load_def]) >>
  irule shape_step_conseq >> irule_at Any compile_store_memory_shape >> simp[]
QED

Resume structlit_iter_elem_copy_shape[bulk]:
  markerLib.RESUME_TAC
  >- (irule shape_step_emit_void_pre >>
      simp[label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, is_label_operand_def, operand_case_not_label]) >>
  irule shape_step_conseq >> irule_at Any compile_imm_copy_to_memory_shape >> simp[]
QED
Finalise structlit_iter_elem_copy_shape

Theorem structlit_array_element_store_shape:
  shape_step F compiler_label
    (\s. cenv_shape_ok s ce /\ cenv_shape_ok s env /\ plain_operand s elem_ptr)
    (case FLOOKUP env.ce_vars id of
       SOME (MemLoc off _) => compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
         elem_size loc (is_slot_addressed loc) fty elem_ty
     | SOME (PtrVar ptr_op _) => compile_iter_elem_copy ce elem_ptr ptr_op
         elem_size loc (is_slot_addressed loc) fty elem_ty
     | _ => emit_void INVALID []) (\u s. T)
Proof
  Cases_on `FLOOKUP env.ce_vars id` >> simp[]
  >- (irule shape_step_emit_void_pre >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def, is_terminator_def]) >>
  rename1 `SOME loc0` >> Cases_on `loc0` >> simp[] >>
  TRY (irule shape_step_emit_void_pre >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def] >> NO_TAC) >>
  irule shape_step_conseq >> irule_at Any structlit_iter_elem_copy_shape >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `cenv_shape_ok _ env` mp_tac >> simp[cenv_shape_ok_def] >> strip_tac >>
  first_x_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  simp[loc_shape_ok_def, plain_operand_def] >> strip_tac >> gvs[is_label_operand_def]
QED

Theorem alloc_run_stmt_array_element_store:
  alloc_run fresh_outputs
    (case FLOOKUP env.ce_vars id of
       SOME (MemLoc off _) => compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
         elem_size loc (is_slot_addressed loc) fty elem_ty
     | SOME (PtrVar ptr_op _) => compile_iter_elem_copy ce elem_ptr ptr_op
         elem_size loc (is_slot_addressed loc) fty elem_ty
     | _ => emit_void INVALID []) (\u s. fresh_outputs s)
Proof
  Cases_on `FLOOKUP env.ce_vars id` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  rename1 `SOME loc0` >> Cases_on `loc0` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
    SRULE [SF ETA_ss] alloc_run_compile_iter_elem_copy]
QED

Theorem alloc_run_stmt_array_after_labels:
  shape_step internal compiler_label (\s. cenv_shape_ok s env)
    (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
    (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T) /\
  compiler_label entry /\ compiler_label cond /\ compiler_label body_lbl /\
  compiler_label incr /\ compiler_label exit /\ exit <> body_lbl ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ cenv_shape_ok s env /\
      plain_operand s arr_op /\ plain_operand s len)
    (do ctr <- (do emit_inst JMP [Label entry] []; new_block entry;
                   ctr <- fresh_var; emit_inst ASSIGN [Lit 0w] [ctr]; return ctr od);
        (if dynamic then
           do invalid <- emit_op GT [len;Lit (n2w capacity)];
              valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
         else comp_return ());
        (do emit_inst JMP [Label cond] []; new_block cond;
            done_op <- emit_op EQ [Var ctr;len];
            emit_inst JNZ [done_op;Label exit;Label body_lbl] [];
            new_block body_lbl od);
        elem_ptr <- (do idx_offset <- emit_op MUL [Var ctr;Lit (n2w elem_size)];
          total_offset <- (if 0 < offset_base then
              emit_op ADD [Lit (n2w offset_base);idx_offset] else comp_return idx_offset);
          emit_op ADD [arr_op;total_offset] od);
        (case FLOOKUP env.ce_vars id of
           SOME (MemLoc off _) => compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
             elem_size loc (is_slot_addressed loc) fty elem_ty
         | SOME (PtrVar ptr_op _) => compile_iter_elem_copy ce elem_ptr ptr_op
             elem_size loc (is_slot_addressed loc) fty elem_ty
         | _ => emit_void INVALID []);
        compile_stmts env (InLoop exit incr) ty stmts;
        emit_jmp_if_not_terminated incr;
        new_block incr; next <- emit_op ADD [Var ctr;Lit 1w];
        emit_inst ASSIGN [next] [ctr]; emit_inst JMP [Label cond] [];
        new_block exit; return () od) (\u s. T)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\ctr s. shape_state s /\
    (cenv_shape_ok s ce /\ cenv_shape_ok s env /\
      plain_operand s arr_op /\ plain_operand s len) /\
    plain_operand s (Var ctr) /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_loop_counter >>
      qexists `\s. cenv_shape_ok s ce /\ cenv_shape_ok s env /\
        plain_operand s arr_op /\ plain_operand s len` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, plain_operand_def, is_label_operand_def,
        SRULE [] (Q.SPEC `[arr_op;len]` shape_stable_plain_operands)]) >>
  qx_gen_tac `ctr` >> simp[comp_ignore_bind_def] >> suspend "capacity"
QED

Resume alloc_run_stmt_array_after_labels[capacity]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ cenv_shape_ok s env /\
    plain_operand s arr_op /\ plain_operand s len /\ plain_operand s (Var ctr))) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any (SRULE [comp_ignore_bind_def] structlit_array_capacity_check_shape) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ cenv_shape_ok s env /\
        plain_operand s arr_op /\ plain_operand s len /\ plain_operand s (Var ctr)`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[arr_op;len;Var ctr]` shape_stable_plain_operands),
        SF ETA_ss, SRULE [comp_ignore_bind_def, SF ETA_ss] alloc_run_stmt_array_capacity_check]) >>
  gen_tac >> simp[] >> suspend "test"
QED

Resume alloc_run_stmt_array_after_labels[test]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ (cenv_shape_ok s ce /\ cenv_shape_ok s env /\
    plain_operand s arr_op /\ plain_operand s (Var ctr))) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_stmt_loop_test) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ cenv_shape_ok s env /\
        plain_operand s arr_op /\ plain_operand s (Var ctr)`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[arr_op;Var ctr]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >> suspend "address"
QED

Resume alloc_run_stmt_array_after_labels[address]:
  irule alloc_run_bind >>
  qexists `\v s. (shape_state s /\ (cenv_shape_ok s ce /\ cenv_shape_ok s env) /\
      plain_operand s v) /\ not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_stmt_array_element_address >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s ce /\ cenv_shape_ok s env`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  qx_gen_tac `elem_ptr` >> simp[] >> suspend "store"
QED

Resume alloc_run_stmt_array_after_labels[store]:
  irule alloc_run_bind >>
  qexists `\u s. (shape_state s /\ cenv_shape_ok s env) /\
    not_fresh_at s ctr /\ ~alloc_owned s ctr` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_frame_reserved >>
      irule_at Any alloc_run_fresh_shape_frame >>
      irule_at Any (SRULE [] structlit_array_element_store_shape) >>
      qexistsl [`ctr`, `\s. cenv_shape_ok s env`] >>
      simp[cenv_shape_ok_stable, SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_stmt_array_element_store]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_stmt_loop_body_tail) >>
  simp[] >> qexistsl [`internal`, `env`] >> simp[]
QED
Finalise alloc_run_stmt_array_after_labels

Theorem alloc_run_compile_stmt_array:
  ce.ce_alloca_locals /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (compile_expr ce (expr_type arr_e) arr_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce (expr_type arr_e) arr_e) (\v s. T) /\
  (!env exit incr. env.ce_alloca_locals /\ env.ce_return_pc = ce.ce_return_pc /\
    compiler_label exit /\ compiler_label incr ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s env)
      (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
      (compile_stmts env (InLoop exit incr) ty stmts) (\u s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lc ty (For id fty (Array arr_e) bound stmts)) (\u s. T)
Proof
  strip_tac >> simp[Once compile_stmt_def, loop_comp_return_bind, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s (vv_operand v)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
      qexistsl [`internal`, `\s. cenv_shape_ok s ce`, `\v s. value_shape_ok s v`,
        `\s. cenv_shape_ok s ce`, `compiler_label`, `\v s. T`] >>
      simp[cenv_shape_ok_stable] >> Cases_on `v` >>
      simp[value_shape_ok_def, vv_operand_def]) >>
  qx_gen_tac `arr_vv` >> BETA_TAC >> suspend "length"
QED

Resume alloc_run_compile_stmt_array[length]:
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ cenv_shape_ok s ce /\
    plain_operand s (vv_operand arr_vv) /\ plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_array_length >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `len_op` >> BETA_TAC >> suspend "commit"
QED

Resume alloc_run_compile_stmt_array[commit]:
  ho_match_mp_tac (SRULE [comp_ignore_bind_def] alloc_run_declare_local_commit_then) >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[vv_operand arr_vv;len_op]` shape_stable_plain_operands)] >>
  qx_gen_tac `env` >> strip_tac >> suspend "labels"
QED

Resume alloc_run_compile_stmt_array[labels]:
  ho_match_mp_tac alloc_run_stmt_loop_labels >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[vv_operand arr_vv;len_op]` shape_stable_plain_operands)] >>
  rpt gen_tac >> strip_tac >> suspend "body"
QED

Resume alloc_run_compile_stmt_array[body]:
  simp[arithmeticTheory.GREATER_DEF] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def, comp_bind_assoc, loop_comp_return_bind]
    alloc_run_stmt_array_after_labels) >> simp[] >>
  qexists `internal` >>
  first_x_assum (drule_at (Pat `_.ce_alloca_locals`)) >> simp[]
QED
Finalise alloc_run_compile_stmt_array
