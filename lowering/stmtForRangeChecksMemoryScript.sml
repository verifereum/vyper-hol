Theory stmtForRangeChecksMemory
Ancestors
  stmtSimForRange emitHelperProps exprLoweringProps fragExec venomInst
  venomState venomExecSemantics list rich_list finite_map words fragGasSeqMem fragGasSeqAbort
  fragGasMode fragGasPathMem fragExecMem memSafeRun instMemFrontier stmtForRangeMemoryParts

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
    (~bad1 /\ ~bad2 ==> run_inst_seq bb.bb_instructions ee = OK s7) /\
    run_inst_seq (TAKE 4 bb.bb_instructions) ee = OK s4 /\
    (~bad1 ==> run_inst_seq (TAKE 7 bb.bb_instructions) ee = OK s6)
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

Theorem for_entry_checked_path_mem:
  !ctx func ee lbl cond_lbl op1 op2 a b cmp cv rv g1 z1 g2 z2 ev bound i.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
        bb_instructions :=
          [mk_inst i ASSIGN [op1] [cv];
           mk_inst (i+1) SUB [op2;op1] [rv];
           mk_inst (i+2) cmp [op1;op2] [g1];
           mk_inst (i+3) ISZERO [Var g1] [z1];
           mk_inst (i+4) ASSERT [Var z1] [];
           mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
           mk_inst (i+6) ISZERO [Var g2] [z2];
           mk_inst (i+7) ASSERT [Var z2] [];
           mk_inst (i+8) ADD [op1;Var rv] [ev];
           mk_inst (i+9) JMP [Label cond_lbl] []] |> /\
    MEM cmp [SGT;GT] /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
    eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
    ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) ==>
    (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
       w2n (b-a) > w2n (n2w bound : bytes32)) ==>
      ?t. gas_marked_path T ctx func ee 0 (Abort Revert_abort t)) /\
    (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
     ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
      ?vs. lookup_var cv (ee with vs_vars := vs) = SOME a /\
           lookup_var ev (ee with vs_vars := vs) = SOME (a+(b-a)) /\
           (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
             lookup_var x (ee with vs_vars := vs) = lookup_var x ee) /\
           gas_marked_path T ctx func ee 0
             (OK (jump_to cond_lbl (ee with vs_vars := vs))))
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block lbl _ = SOME bb` >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt a b else w2n a > w2n b` >>
  qabbrev_tac `bad2 = (w2n (b-a) > w2n (n2w bound : bytes32))` >>
  qabbrev_tac `s1 = update_var cv a ee` >>
  qabbrev_tac `s2 = update_var rv (b-a) s1` >>
  qabbrev_tac `s3 = update_var g1 (bool_to_word bad1) s2` >>
  qabbrev_tac `s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3` >>
  qabbrev_tac `s5 = update_var g2 (bool_to_word bad2) s4` >>
  qabbrev_tac `s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5` >>
  qabbrev_tac `s7 = update_var ev (a+(b-a)) s6` >>
  qabbrev_tac `bb9 = bb with bb_instructions := TAKE 9 bb.bb_instructions` >>
  `bb9.bb_instructions =
     [mk_inst i ASSIGN [op1] [cv]; mk_inst (i+1) SUB [op2;op1] [rv];
      mk_inst (i+2) cmp [op1;op2] [g1]; mk_inst (i+3) ISZERO [Var g1] [z1];
      mk_inst (i+4) ASSERT [Var z1] [];
      mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
      mk_inst (i+6) ISZERO [Var g2] [z2]; mk_inst (i+7) ASSERT [Var z2] [];
      mk_inst (i+8) ADD [op1;Var rv] [ev]]` by simp[Abbr `bb9`, Abbr `bb`] >>
  map_every (fn q => qpat_assum q
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (bad1 = _)`, `Abbrev (bad2 = _)`, `Abbrev (s1 = _)`,
     `Abbrev (s2 = _)`, `Abbrev (s3 = _)`, `Abbrev (s4 = _)`,
     `Abbrev (s5 = _)`, `Abbrev (s6 = _)`, `Abbrev (s7 = _)`] >>
  drule_all for_checked_entry_finite >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`bad1 = _`, `bad2 = _`, `s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`,
     `s5 = _`, `s6 = _`, `s7 = _`, `bb9.bb_instructions = _`,
     `bad1 ==> _`, `~bad1 /\ bad2 ==> _`] >>
  qpat_x_assum `Abbrev (bb9 = _)` (fn th =>
    rule_assum_tac (SIMP_RULE (srw_ss())
      [REWRITE_RULE [markerTheory.Abbrev_def] th, TAKE_TAKE_MIN,
       Excl "MEM", Excl "ALL_DISTINCT"])) >>
  suspend "prefix_paths"
QED

Resume for_entry_checked_path_mem[prefix_paths]:
  `!k t. k <= 9 /\ run_inst_seq (TAKE k bb.bb_instructions) ee = OK t ==>
     gas_path_mem ctx func ee 0 (OK (t with vs_inst_idx := k))` by
    (rpt gen_tac >> strip_tac >>
     `LENGTH (TAKE k bb.bb_instructions) = k` by simp[Abbr `bb`] >>
     `FILTER (\inst. inst.inst_opcode = GAS) (TAKE k bb.bb_instructions) = []` by
       (rewrite_tac[FILTER_EQ_NIL] >> irule EVERY_TAKE >>
        qpat_x_assum `Abbrev (bb = _)` mp_tac >>
        qpat_x_assum `cmp = SGT \/ cmp = GT` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        simp[Abbr `bb`, mk_inst_def]) >>
     `0 = LENGTH (FILTER (\inst. inst.inst_opcode = GAS)
         (TAKE k bb.bb_instructions))` by simp[] >>
     pop_assum SUBST1_TAC >>
     `t with vs_inst_idx := k =
        t with vs_inst_idx := ee.vs_inst_idx + LENGTH (TAKE k bb.bb_instructions)` by simp[] >>
     pop_assum SUBST1_TAC >> irule run_inst_seq_gas_path_mem >>
     simp[] >>
     conj_tac >-
       (`TAKE k bb.bb_instructions = TAKE k (TAKE 9 bb.bb_instructions)` by
          (qpat_x_assum `k <= 9` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
           strip_tac >> simp[TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >>
           IF_CASES_TAC >> simp[] >> `k = 9` by decide_tac >> simp[]) >>
        pop_assum SUBST1_TAC >> irule EVERY_TAKE >>
        qpat_x_assum `Abbrev (bb = _)` mp_tac >>
        qpat_x_assum `cmp = SGT \/ cmp = GT` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        simp[Abbr `bb`, mk_inst_def, is_terminator_def]) >>
     conj_tac >- (simp[IS_PREFIX_APPEND] >> qexists_tac `DROP k bb.bb_instructions` >> simp[TAKE_DROP]) >>
     irule run_inst_seq_mem_ok_every >> irule EVERY_TAKE >>
     qpat_x_assum `Abbrev (bb = _)` mp_tac >>
     qpat_x_assum `cmp = SGT \/ cmp = GT` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     simp[Abbr `bb`, mk_inst_def, below_frontier_no_ranges,
          inst_dload_in_section_other]) >>
  suspend "path_cases"
QED

Resume for_entry_checked_path_mem[path_cases]:
  conj_tac
  >- (disch_tac >> Cases_on `bad1`
      >- (`gas_path_mem ctx func ee 0 (OK (s4 with vs_inst_idx := 4))` by
            (first_x_assum irule >> simp[]) >>
          `step_inst_base (mk_inst (i+4) ASSERT [Var z1] [])
             (s4 with vs_inst_idx := 4) =
             Abort Revert_abort
               (revert_state (set_returndata [] (s4 with vs_inst_idx := 4)))` by
            (irule step_ASSERT_revert >>
             simp[Abbr `s4`, eval_operand_def, lookup_var_def, update_var_def, bool_to_word_def, FLOOKUP_UPDATE]) >>
          drule_at (Pat `step_inst_base _ _ = _`) gas_marked_path_abort >>
          simp[mk_inst_def, is_terminator_def, below_frontier_no_ranges,
               inst_dload_in_section_other] >>
          disch_then (qspecl_then [`T`, `ctx`, `func`, `bb`] mp_tac) >>
          (impl_tac >-
            simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
                 update_var_def, Abbr `bb`, get_instruction_def, mk_inst_def]) >>
          strip_tac >>
          qexists_tac `revert_state (set_returndata [] (s4 with vs_inst_idx := 4))` >>
          `gas_marked_path T ctx func ee 0 (OK (s4 with vs_inst_idx := 4))` by
             simp[gas_marked_path_def] >>
          drule_all gas_marked_path_then >> simp[]) >>
      `bad2` by metis_tac[] >>
      `gas_path_mem ctx func ee 0 (OK (s6 with vs_inst_idx := 7))` by
        (first_x_assum irule >> simp[]) >>
      `step_inst_base (mk_inst (i+7) ASSERT [Var z2] [])
         (s6 with vs_inst_idx := 7) =
         Abort Revert_abort
           (revert_state (set_returndata [] (s6 with vs_inst_idx := 7)))` by
        (irule step_ASSERT_revert >>
         simp[Abbr `s6`, eval_operand_def, lookup_var_def, update_var_def,
              bool_to_word_def, FLOOKUP_UPDATE]) >>
      drule_at (Pat `step_inst_base _ _ = _`) gas_marked_path_abort >>
      simp[mk_inst_def, is_terminator_def, below_frontier_no_ranges,
           inst_dload_in_section_other] >>
      disch_then (qspecl_then [`T`, `ctx`, `func`, `bb`] mp_tac) >>
      (impl_tac >-
        simp[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
             update_var_def, Abbr `bb`, get_instruction_def, mk_inst_def]) >>
      strip_tac >>
      qexists_tac `revert_state (set_returndata [] (s6 with vs_inst_idx := 7))` >>
      `gas_marked_path T ctx func ee 0 (OK (s6 with vs_inst_idx := 7))` by
         simp[gas_marked_path_def] >>
      drule_all gas_marked_path_then >> simp[]) >>
  suspend "success"
QED

Resume for_entry_checked_path_mem[success]:
  strip_tac >>
  `gas_path_mem ctx func ee 0 (OK (s7 with vs_inst_idx := 9))` by
    (first_x_assum irule >> simp[]) >>
  `step_inst_base (mk_inst (i+9) JMP [Label cond_lbl] [])
     (s7 with vs_inst_idx := 9) = OK (jump_to cond_lbl (s7 with vs_inst_idx := 9))` by
    simp[step_inst_base_def, mk_inst_def] >>
  drule_at (Pat `step_inst_base _ _ = _`) for_range_jump_at_zero_path_mem >>
  simp[mk_inst_def, is_terminator_def, below_frontier_no_ranges,
       inst_dload_in_section_other] >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >-
    simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
         update_var_def, Abbr `bb`, get_instruction_def, mk_inst_def]) >>
  strip_tac >>
  `gas_path_mem ctx func ee 0 (OK (jump_to cond_lbl s7))` by
    (drule_all gas_path_mem_then >> simp[jump_to_def]) >>
  qexists_tac `s7.vs_vars` >>
  `ee with vs_vars := s7.vs_vars = s7` by
    simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
         update_var_def] >>
  simp[gas_marked_path_def] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  map_every (fn q => qpat_x_assum q mp_tac)
    [`Abbrev (s7 = _)`, `Abbrev (s6 = _)`, `Abbrev (s5 = _)`,
     `Abbrev (s4 = _)`, `Abbrev (s3 = _)`, `Abbrev (s2 = _)`, `Abbrev (s1 = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[ALL_DISTINCT, EQ_SYM_EQ]
QED

Finalise for_entry_checked_path_mem
