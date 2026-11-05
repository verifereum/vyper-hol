Theory stmtForRangeChecksMemory
Ancestors
  stmtSimForRange emitHelperProps exprLoweringProps fragExec venomInst
  venomState venomExecSemantics list words

Theorem for_checked_entry_finite:
  !ee bb op1 op2 a b cmp cv rv g1 z1 g2 z2 ev bound i
   bad1 bad2 s1 s2 s3 s4 s5 s6 s7.
    bb.bb_instructions =
      [mk_inst i ASSIGN [op1] [cv];
       mk_inst (i+1) SUB [op2;op1] [rv];
       mk_inst (i+2) cmp [op1;op2] [g1];
       mk_inst (i+3) ISZERO [Var g1] [z1];
       mk_inst (i+4) ASSERT [Var z1] [];
       mk_inst (i+5) GT [Var rv; Lit (n2w bound)] [g2];
       mk_inst (i+6) ISZERO [Var g2] [z2];
       mk_inst (i+7) ASSERT [Var z2] [];
       mk_inst (i+8) ADD [op1;Var rv] [ev]] /\
    MEM cmp [SGT;GT] /\
    eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
    ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
    bad1 = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
    bad2 = (w2n (b-a) > w2n (n2w bound : bytes32)) /\
    s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
    s3 = update_var g1 (bool_to_word bad1) s2 /\
    s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3 /\
    s5 = update_var g2 (bool_to_word bad2) s4 /\
    s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5 /\
    s7 = update_var ev (a+(b-a)) s6 ==>
    (bad1 ==> run_inst_seq (TAKE 5 bb.bb_instructions) ee =
       Abort Revert_abort (revert_state (set_returndata [] s4))) /\
    (~bad1 /\ bad2 ==> run_inst_seq (TAKE 8 bb.bb_instructions) ee =
       Abort Revert_abort (revert_state (set_returndata [] s6))) /\
    (~bad1 /\ ~bad2 ==> run_inst_seq bb.bb_instructions ee = OK s7)
Proof
  rpt gen_tac >> strip_tac >>
  `!x w s. MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
       eval_operand op1 (update_var x w s) = eval_operand op1 s /\
       eval_operand op2 (update_var x w s) = eval_operand op2 s` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `op1` >> Cases_on `op2` >>
     simp[eval_operand_def, lookup_var_update_var, update_var_def] >>
     metis_tac[]) >>
  `!s. (s = s1 \/ s = s2 \/ s = s3 \/ s = s4 \/ s = s5 \/ s = s6) ==>
       eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b` by
    (rpt strip_tac >> first_x_assum SUBST1_TAC >> simp[]) >>
  `eval_operand (Var rv) s4 = SOME (b-a) /\
   eval_operand (Var rv) s6 = SOME (b-a) /\
   eval_operand (Var g1) s3 = SOME (bool_to_word bad1) /\
   eval_operand (Var z1) s4 = SOME (bool_to_word (bool_to_word bad1 = 0w)) /\
   eval_operand (Var g2) s5 = SOME (bool_to_word bad2) /\
   eval_operand (Var z2) s6 = SOME (bool_to_word (bool_to_word bad2 = 0w))` by
    (gvs[ALL_DISTINCT, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst i ASSIGN [op1] [cv]) ee = OK s1` by
    simp[step_inst_base_def, mk_inst_def] >>
  `step_inst_base (mk_inst (i+1) SUB [op2;op1] [rv]) s1 = OK s2` by
    (simp[] >> irule step_SUB >> metis_tac[]) >>
  `step_inst_base (mk_inst (i+2) cmp [op1;op2] [g1]) s2 = OK s3` by
    (simp[] >> Cases_on `cmp = SGT`
     >- (gvs[] >> irule step_SGT >> metis_tac[]) >>
     gvs[] >> irule step_GT >> metis_tac[]) >>
  `step_inst_base (mk_inst (i+3) ISZERO [Var g1] [z1]) s3 = OK s4` by
    (qpat_assum `s4 = _` (fn th => pure_once_rewrite_tac [th]) >>
     irule step_ISZERO >> first_assum ACCEPT_TAC) >>
  `run_inst_seq (TAKE 4 bb.bb_instructions) ee = OK s4` by
    (map_every (fn q => qpat_x_assum q kall_tac)
       [`s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`] >>
     simp[run_inst_seq_def]) >>
  suspend "suffix"
QED

Resume for_checked_entry_finite[suffix]:
  Cases_on `bad1`
  >- (`step_inst_base (mk_inst (i+4) ASSERT [Var z1] []) s4 =
         Abort Revert_abort (revert_state (set_returndata [] s4))` by
        (irule step_ASSERT_revert >> gvs[bool_to_word_def]) >>
      `TAKE 5 bb.bb_instructions = TAKE 4 bb.bb_instructions ++
         [mk_inst (i+4) ASSERT [Var z1] []]` by simp[] >>
      pop_assum SUBST1_TAC >>
      drule run_inst_seq_append >> disch_then (pure_rewrite_tac o single) >>
      map_every (fn q => qpat_x_assum q kall_tac)
        [`s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`] >>
      simp[run_inst_seq_def]) >>
  `step_inst_base (mk_inst (i+4) ASSERT [Var z1] []) s4 = OK s4` by
    (irule step_ASSERT_ok >> gvs[bool_to_word_def]) >>
  `step_inst_base (mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2]) s4 = OK s5` by
    (qpat_assum `s5 = _` (fn th => pure_once_rewrite_tac [th]) >>
     qpat_assum `bad2 = _` (fn th => pure_once_rewrite_tac [th]) >>
     irule step_GT >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (i+6) ISZERO [Var g2] [z2]) s5 = OK s6` by
    (qpat_assum `s6 = _` (fn th => pure_once_rewrite_tac [th]) >>
     irule step_ISZERO >> first_assum ACCEPT_TAC) >>
  `run_inst_seq (TAKE 7 bb.bb_instructions) ee = OK s6` by
    (`TAKE 7 bb.bb_instructions = TAKE 4 bb.bb_instructions ++
       [mk_inst (i+4) ASSERT [Var z1] [];
        mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
        mk_inst (i+6) ISZERO [Var g2] [z2]]` by simp[] >>
     pop_assum SUBST1_TAC >>
     drule run_inst_seq_append >> disch_then (pure_rewrite_tac o single) >>
     map_every (fn q => qpat_x_assum q kall_tac)
       [`s4 = _`, `s5 = _`, `s6 = _`] >> simp[run_inst_seq_def]) >>
  suspend "last"
QED

Resume for_checked_entry_finite[last]:
  Cases_on `bad2`
  >- (`step_inst_base (mk_inst (i+7) ASSERT [Var z2] []) s6 =
         Abort Revert_abort (revert_state (set_returndata [] s6))` by
        (irule step_ASSERT_revert >> gvs[bool_to_word_def]) >>
      `TAKE 8 bb.bb_instructions = TAKE 7 bb.bb_instructions ++
         [mk_inst (i+7) ASSERT [Var z2] []]` by simp[] >>
      pop_assum SUBST1_TAC >>
      drule run_inst_seq_append >>
      disch_then (pure_rewrite_tac o single) >>
      map_every (fn q => qpat_x_assum q kall_tac)
        [`s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`, `s5 = _`, `s6 = _`] >>
      simp[run_inst_seq_def]) >>
  `step_inst_base (mk_inst (i+7) ASSERT [Var z2] []) s6 = OK s6` by
    (irule step_ASSERT_ok >> gvs[bool_to_word_def]) >>
  `step_inst_base (mk_inst (i+8) ADD [op1;Var rv] [ev]) s6 = OK s7` by
    (qpat_assum `s7 = _` (fn th => pure_once_rewrite_tac [th]) >>
     irule step_ADD >> metis_tac[]) >>
  `bb.bb_instructions = TAKE 7 bb.bb_instructions ++
     [mk_inst (i+7) ASSERT [Var z2] [];
      mk_inst (i+8) ADD [op1;Var rv] [ev]]` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule run_inst_seq_append >>
  disch_then (pure_rewrite_tac o single) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`, `s5 = _`, `s6 = _`, `s7 = _`] >>
  simp[run_inst_seq_def]
QED
Finalise for_checked_entry_finite
