Theory bodyPtrStructLitLoopShapeCopy
Ancestors bodyPtrStructLitLoopShapeMemory bodyPtrStructLitLoopShapeTail
  bodyPtrStructLitLoopShapeControl loweringShapeProps loweringShapeRules
  loweringShapeDefs context compileEnv bodyPtrStructLitLoopShapeEmit
  bodyPtrStructLitEmitterFrame stackPlanTypes

Theorem loop_shape_copy_body:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s src /\ plain_operand s dst /\
      plain_operand s (Var ctr))
    (do src_off <- (if ss = 1 then emit_op ADD [src; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ss)];
                 emit_op ADD [src; scaled] od);
        loaded <- compile_ptr_load ctor NONE ll src_off;
        dst_off <- (if ds = 1 then emit_op ADD [dst; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ds)];
                 emit_op ADD [dst; scaled] od);
        compile_ptr_store ctor NONE sl dst_off loaded od)
    (\u s. R s /\ plain_operand s src /\ plain_operand s dst /\
      plain_operand s (Var ctr))
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. (R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_offset >>
      qexists `\s. R s /\ plain_operand s dst` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `a` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\v s. (R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_frame >>
      simp[compile_ptr_load_none_shape, shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `v` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\b s. ((R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v) /\ plain_operand s b` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_offset >>
      qexists `\s. R s /\ plain_operand s src /\ plain_operand s v` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `b` >> BETA_TAC >> irule shape_step_conseq >>
  irule_at Any loop_shape_ptr_store >>
  qexists `\s. R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED

Theorem loop_shape_copy_tail:
  compiler_label cond /\ compiler_label exit ==>
  shape_step F compiler_label
    (\s. plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
    (do (do src_off <- (if ss = 1 then emit_op ADD [src; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ss)];
                 emit_op ADD [src; scaled] od);
        loaded <- compile_ptr_load ctor NONE ll src_off;
        dst_off <- (if ds = 1 then emit_op ADD [dst; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ds)];
                 emit_op ADD [dst; scaled] od);
        compile_ptr_store ctor NONE sl dst_off loaded od);
        next <- emit_op ADD [Var ctr; Lit 1w];
        emit_inst ASSIGN [next] [ctr];
        emit_inst JMP [Label cond] [];
        new_block exit od) (\u s. T)
Proof
  strip_tac >> irule shape_step_ignore_bind >>
  qexists `\u s. plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr)` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_copy_body >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_conseq >>
  irule_at Any loop_shape_increment_exit >>
  qexists `\s. plain_operand s src /\ plain_operand s dst` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED

Theorem loop_shape_copy_header:
  compiler_label cond /\ compiler_label body_lbl /\ compiler_label exit /\ exit <> body_lbl ==>
  shape_step F compiler_label
    (\s. plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
    (do emit_inst ASSIGN [Lit 0w] [ctr];
        emit_inst JMP [Label cond] []; new_block cond;
        test <- emit_op EQ [Var ctr; Lit (n2w n)];
        emit_inst JNZ [test; Label exit; Label body_lbl] []; new_block body_lbl;
        src_off <- (if ss = 1 then emit_op ADD [src; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ss)];
                 emit_op ADD [src; scaled] od);
        loaded <- compile_ptr_load ctor NONE ll src_off;
        dst_off <- (if ds = 1 then emit_op ADD [dst; Var ctr]
         else do scaled <- emit_op MUL [Var ctr; Lit (n2w ds)];
                 emit_op ADD [dst; scaled] od);
        compile_ptr_store ctor NONE sl dst_off loaded;
        next <- emit_op ADD [Var ctr; Lit 1w];
        emit_inst ASSIGN [next] [ctr]; emit_inst JMP [Label cond] [];
        new_block exit od) (\u s. T)
Proof
  strip_tac >> irule loop_shape_header >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >> reverse conj_tac
  >- (ho_match_mp_tac loop_shape_op >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
        SRULE [is_label_operand_def]
          (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
      rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  mp_tac (SRULE [comp_ignore_bind_def, comp_bind_assoc] loop_shape_copy_tail) >>
  simp[comp_ignore_bind_def]
QED

Theorem loop_shape_word_copy:
  shape_step F compiler_label
    (\s. plain_operand s src /\ plain_operand s dst)
    (compile_word_copy_loop src dst n ll sl ctor) (\u s. T)
Proof
  simp[compile_word_copy_loop_def] >> irule shape_step_bind >>
  qexists `\l s. (plain_operand s src /\ plain_operand s dst) /\ compiler_label l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `cond` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\l s. ((plain_operand s src /\ plain_operand s dst) /\ compiler_label cond) /\
    compiler_label l /\ label_sfx "wcopy_body" l` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      simp[shape_stable_conj, shape_stable_def,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `bl` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\l s. (((plain_operand s src /\ plain_operand s dst) /\ compiler_label cond) /\
    compiler_label bl /\ label_sfx "wcopy_body" bl) /\
    compiler_label l /\ label_sfx "wcopy_exit" l` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      simp[shape_stable_conj, shape_stable_def,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ex` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\c s. ((((plain_operand s src /\ plain_operand s dst) /\ compiler_label cond) /\
    compiler_label bl /\ label_sfx "wcopy_body" bl) /\
    compiler_label ex /\ label_sfx "wcopy_exit" ex) /\ plain_operand s (Var c)` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_var >>
      simp[shape_stable_conj, shape_stable_def,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ctr` >> BETA_TAC >>
  Cases_on `compiler_label cond /\ compiler_label bl /\ compiler_label ex /\ ex <> bl`
  >- (irule shape_step_conseq >> irule_at Any loop_shape_copy_header >>
      simp[] >> gvs[]) >>
  simp[shape_step_def] >> rpt strip_tac >>
  `ex <> bl` by
    (irule label_sfx_distinct >> qexistsl [`"wcopy_exit"`, `"wcopy_body"`] >> simp[]) >>
  gvs[]
QED
