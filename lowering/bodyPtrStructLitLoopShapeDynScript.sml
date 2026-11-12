Theory bodyPtrStructLitLoopShapeDyn
Ancestors bodyPtrStructLitLoopShapeDynBody bodyPtrStructLitLoopShapeEmit
  bodyPtrStructLitEmitterFrame loweringShapeRules loweringShapeDefs compileEnv
  stackPlanTypes context

Theorem loop_shape_dynarray_to_storage:
  shape_step F compiler_label
    (\s. plain_operand s src /\ plain_operand s dst)
    (compile_dynarray_to_storage src dst ew ems transient) (\u s. T)
Proof
  simp[compile_dynarray_to_storage_def] >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >> simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `len` >> irule shape_step_bind >>
  qexists `\l s. ((plain_operand s src /\ plain_operand s dst) /\ plain_operand s len) /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      simp[shape_stable_conj, SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `cond` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\l s. (((plain_operand s src /\ plain_operand s dst) /\ plain_operand s len) /\ compiler_label cond) /\
    compiler_label l /\ label_sfx "dyn_body" l` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `bl` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\l s. ((((plain_operand s src /\ plain_operand s dst) /\ plain_operand s len) /\ compiler_label cond) /\
    compiler_label bl /\ label_sfx "dyn_body" bl) /\
    compiler_label l /\ label_sfx "dyn_exit" l` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ex` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\c s. (((((plain_operand s src /\ plain_operand s dst) /\ plain_operand s len) /\ compiler_label cond) /\
    compiler_label bl /\ label_sfx "dyn_body" bl) /\
    compiler_label ex /\ label_sfx "dyn_exit" ex) /\ plain_operand s (Var c)` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >>
      simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ctr` >> BETA_TAC >>
  Cases_on `compiler_label cond /\ compiler_label bl /\ compiler_label ex /\ ex <> bl`
  >- (simp[comp_ignore_bind_def] >> irule shape_step_conseq >>
      irule_at Any (SRULE [comp_ignore_bind_def, comp_bind_assoc] loop_shape_dyn_header) >>
      qexists `\s. plain_operand s src /\ plain_operand s dst /\ plain_operand s len /\ plain_operand s (Var ctr)` >>
      gvs[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      qexists `\u s. T` >>
      mp_tac (Q.INST [`exit` |-> `ex`] loop_shape_dyn_body) >>
      Cases_on `ew = 1` >> simp[comp_ignore_bind_def, comp_bind_assoc, loop_comp_return_bind]) >>
  simp[shape_step_def] >> rpt strip_tac >>
  `ex <> bl` by
    (irule label_sfx_distinct >> qexistsl [`"dyn_exit"`, `"dyn_body"`] >> simp[]) >> gvs[]
QED
