Theory bodyPtrStructLitLoopShapeDynBody
Ancestors bodyPtrStructLitLoopShapeDynAddress bodyPtrStructLitLoopShapeCopy
  bodyPtrStructLitLoopShapeEmit bodyPtrStructLitLoopShapeTail
  bodyPtrStructLitEmitterFrame loweringShapeRules loweringShapeDefs compileEnv
  stackPlanTypes context bodyPtrStructLitLoopShapeControl

Theorem loop_comp_return_bind:
  comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem loop_shape_storage_store:
  shape_stable R /\ (!s. R s ==> plain_operand s dst /\ plain_operand s v) ==>
  shape_step F compiler_label R
    (if transient then emit_void TSTORE [dst; v] else emit_void SSTORE [dst; v])
    (\u s. R s)
Proof
  strip_tac >> IF_CASES_TAC >> ho_match_mp_tac loop_shape_void >> simp[] >>
  rpt strip_tac >> first_assum drule >> strip_tac >> simp[] >>
  irule (cj 2 loop_extra_data_inst_ok) >> simp[] >> qexists `s` >> simp[]
QED

Theorem loop_shape_dyn_single_copy:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
    (do p <- (do m <- emit_op MUL [Var ctr; Lit 32w];
                 off <- emit_op ADD [Lit 32w; m]; emit_op ADD [src; off] od);
        v <- emit_op MLOAD [p];
        d <- (do off <- emit_op ADD [Var ctr; Lit 1w]; emit_op ADD [dst; off] od);
        (if transient then emit_void TSTORE [d; v] else emit_void SSTORE [d; v]) od)
    (\u s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. (R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_index_address >>
      qexists `\s. R s /\ plain_operand s dst` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `p` >> BETA_TAC >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `v` >> irule shape_step_bind >>
  qexists `\d s. ((R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v) /\ plain_operand s d` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_single_slot_address >>
      qexists `\s. R s /\ plain_operand s src /\ plain_operand s v` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `d` >> BETA_TAC >> irule shape_step_conseq >>
  irule_at Any loop_shape_storage_store >>
  qexists `\s. ((R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v) /\ plain_operand s d` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  gvs[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

Theorem loop_shape_dyn_multi_copy:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
    (do p <- (do m <- emit_op MUL [Var ctr; Lit (n2w ems)];
                 off <- emit_op ADD [Lit 32w; m]; emit_op ADD [src; off] od);
        d <- (do m <- emit_op MUL [Var ctr; Lit (n2w ew)];
                 off <- emit_op ADD [Lit 1w; m]; emit_op ADD [dst; off] od);
        compile_word_copy_loop p d ew LocMemory
          (if transient then LocTransient else LocStorage) F; return () od)
    (\u s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr))
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. (R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_index_address >>
      qexists `\s. R s /\ plain_operand s dst` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `p` >> BETA_TAC >> irule shape_step_bind >>
  qexists `\d s. ((R s /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)) /\ plain_operand s p) /\ plain_operand s d` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_index_address >>
      qexists `\s. R s /\ plain_operand s src /\ plain_operand s p` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  qx_gen_tac `d` >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists `\u s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr)` >>
  reverse conj_tac
  >- (irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any loop_shape_word_copy >>
      qexists `\s. R s /\ plain_operand s src /\ plain_operand s dst /\ plain_operand s (Var ctr)` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> simp[shape_step_return]
QED

Theorem loop_shape_dyn_finish:
  shape_stable R /\ compiler_label cond /\ compiler_label exit ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s dst /\ plain_operand s len /\ plain_operand s (Var ctr))
    (do (do next <- emit_op ADD [Var ctr; Lit 1w];
            emit_inst ASSIGN [next] [ctr]; emit_inst JMP [Label cond] [];
            new_block exit od);
        (if transient then emit_void TSTORE [dst; len] else emit_void SSTORE [dst; len]) od)
    (\u s. R s /\ plain_operand s dst /\ plain_operand s len /\ plain_operand s (Var ctr))
Proof
  strip_tac >> irule shape_step_ignore_bind >>
  qexists `\u s. R s /\ plain_operand s dst /\ plain_operand s len /\ plain_operand s (Var ctr)` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any loop_shape_increment_exit >>
      qexists `\s. R s /\ plain_operand s dst /\ plain_operand s len` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> ho_match_mp_tac loop_shape_storage_store >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED

Theorem loop_shape_dyn_test:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ plain_operand s (Var ctr) /\ plain_operand s len)
    (do lt_op <- emit_op LT [Var ctr; len]; emit_op ISZERO [lt_op] od)
    (\v s. (R s /\ plain_operand s (Var ctr) /\ plain_operand s len) /\ plain_operand s v)
Proof
  strip_tac >> irule loop_shape_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >> conj_tac
  >- (rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `lt_op` >> irule shape_step_conseq >> irule_at Any loop_shape_op >>
  qexists `\s. (R s /\ plain_operand s (Var ctr) /\ plain_operand s len) /\
    plain_operand s lt_op` >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
  rpt strip_tac >> irule (cj 2 loop_extra_data_inst_ok) >>
  simp[] >> qexists `s` >> simp[]
QED

Theorem loop_shape_dyn_body:
  compiler_label cond /\ compiler_label exit ==>
  shape_step F compiler_label
    (\s. plain_operand s src /\ plain_operand s dst /\ plain_operand s len /\
      plain_operand s (Var ctr))
    (do (if ew = 1 then
          do p <- (do m <- emit_op MUL [Var ctr; Lit 32w];
                      off <- emit_op ADD [Lit 32w; m]; emit_op ADD [src; off] od);
             v <- emit_op MLOAD [p];
             d <- (do off <- emit_op ADD [Var ctr; Lit 1w]; emit_op ADD [dst; off] od);
             (if transient then emit_void TSTORE [d; v] else emit_void SSTORE [d; v]) od
         else
          do p <- (do m <- emit_op MUL [Var ctr; Lit (n2w ems)];
                      off <- emit_op ADD [Lit 32w; m]; emit_op ADD [src; off] od);
             d <- (do m <- emit_op MUL [Var ctr; Lit (n2w ew)];
                      off <- emit_op ADD [Lit 1w; m]; emit_op ADD [dst; off] od);
             compile_word_copy_loop p d ew LocMemory
               (if transient then LocTransient else LocStorage) F; return () od);
        (do (do next <- emit_op ADD [Var ctr; Lit 1w];
                emit_inst ASSIGN [next] [ctr]; emit_inst JMP [Label cond] [];
                new_block exit od);
            (if transient then emit_void TSTORE [dst; len] else emit_void SSTORE [dst; len]) od) od)
    (\u s. T)
Proof
  strip_tac >> irule shape_step_ignore_bind >>
  qexists `\u s. plain_operand s len /\ plain_operand s src /\ plain_operand s dst /\
    plain_operand s (Var ctr)` >> reverse conj_tac
  >- (IF_CASES_TAC
      >- (irule shape_step_conseq >> irule_at Any loop_shape_dyn_single_copy >>
          qexists `\s. plain_operand s len` >>
          simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
      irule shape_step_conseq >> irule_at Any loop_shape_dyn_multi_copy >>
      qexists `\s. plain_operand s len` >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
  gen_tac >> BETA_TAC >> irule shape_step_conseq >>
  irule_at Any loop_shape_dyn_finish >> qexists `\s. plain_operand s src` >>
  simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED

Theorem loop_shape_dyn_header:
  shape_stable R /\ compiler_label cond /\ compiler_label body_lbl /\ compiler_label exit /\
  exit <> body_lbl /\ (!s. R s ==> plain_operand s (Var ctr) /\ plain_operand s len) /\
  shape_step F compiler_label R body_code Q ==>
  shape_step F compiler_label R
    (do emit_inst ASSIGN [Lit 0w] [ctr]; emit_inst JMP [Label cond] [];
        new_block cond;
        test <- (do lt_op <- emit_op LT [Var ctr; len]; emit_op ISZERO [lt_op] od);
        emit_inst JNZ [test; Label exit; Label body_lbl] []; new_block body_lbl;
        body_code od) Q
Proof
  strip_tac >> irule loop_shape_header >> simp[] >>
  irule shape_step_conseq >> irule_at Any loop_shape_dyn_test >>
  qexists `R` >> simp[]
QED
