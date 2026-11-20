(* The conditional-jump rewrite uses the existing bounded path checkpoints. *)
Theory asmOptWithinInefficient
Ancestors
  asmSpliceWithinOwn asmSpliceWithin asmSpliceOwn asmSplice asmFinalizerPrefixInefficient
  asmOptInefficientJumps asmSymOwnCode asmSymPc asmSymPcOwn asmSymSem asmSymSemWithin asmSem
  asmOptimizer asmWf symbolResolve arithmetic list

Theorem own_terminal_checkpoint[local]:
  !n ss. sym_terminal (sym_steps_own p env own n ss) ==>
    ?i a. i < n /\ sym_steps_own p env own i ss = SymOK a /\
      a.sym_base.as_pc < LENGTH p /\
      sym_terminal (sym_step_own p env own (EL a.sym_base.as_pc p) a)
Proof
  Induct >- simp[sym_steps_own_def, sym_terminal_def] >>
  gen_tac >> simp[sym_steps_own_def] >>
  IF_CASES_TAC >> simp[sym_terminal_def] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >>
  simp[sym_terminal_def]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      qexistsl_tac [`SUC i`, `a`] >> simp[sym_steps_own_def]) >>
  qexistsl_tac [`0`, `ss`] >> simp[sym_steps_own_def, sym_terminal_def]
QED

Theorem inefficient_window_within_own[local]:
  asm_static_wf
    (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest) ==>
  own_window_within pre [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]
    [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] (AsmLabel x :: rest)
Proof
  disch_tac >>
  mp_tac (Q.INST [
    `pat` |-> `[AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]`,
    `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`,
    `post` |-> `AsmLabel x :: rest`] own_window_plain_within) >>
  (impl_tac >- suspend "certificate") >> disch_then ACCEPT_TAC
QED

Resume inefficient_window_within_own[certificate]:
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++
    AsmLabel x :: rest` >>
  qabbrev_tac `q = pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest` >>
  mp_tac (Q.SPECL [`pre`, `x`, `y`, `rest`, `env`, `ss`]
    inefficient_jump_window_with_bounds) >>
  (impl_tac >- fs[Abbr `p`]) >> strip_tac >>
  `!n. n <= d ==> sym_steps_own p env own n ss = sym_steps p env n ss` by
    (rpt strip_tac >> irule sym_steps_own_eq_without_code_reads >>
     rpt strip_tac >> `i < d` by decide_tac >>
     qpat_x_assum `!i a. i < d /\ _ ==> _`
       (qspecl_then [`i`, `t`] mp_tac) >>
     (impl_tac >- fs[Abbr `p`]) >> strip_tac >>
     `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
     gvs[Abbr `p`, EL_APPEND_EQN]) >>
  `!n. n <= 3 ==> sym_steps_own q env own n ss = sym_steps q env n ss` by
    (rpt strip_tac >> simp_tac bool_ss [Abbr `q`] >>
     irule sym_steps_own_agree_on_chunk >> simp[]) >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmPushLabel x` by
    simp[Abbr `p`, EL_APPEND_EQN] >>
  `2 <= d` by
    (spose_not_then strip_assume_tac >> `d = 1` by decide_tac >> gvs[] >>
     qabbrev_tac `a = ss with <|sym_base := asm_next ss.sym_base;
                                  sym_stack := Lab x 0 :: ss.sym_stack|>` >>
     `sym_steps p env 1 ss = SymOK a` by
       simp[sym_steps_pos, sym_steps_def, sym_step_push_label, Abbr `a`] >>
     qpat_x_assum `!a. sym_steps _ _ 1 _ = _ ==> _`
       (qspec_then `a` mp_tac) >>
     simp[Abbr `p`, Abbr `a`, asm_next_def]) >>
  `!i a. i < d /\ sym_steps_own p env own i ss = SymOK a ==>
    a.sym_base.as_pc = LENGTH pre + i` by
    (rpt strip_tac >> `i <= d` by decide_tac >> fs[Abbr `p`] >> metis_tac[]) >>
  `sym_prefix_all (sym_steps_own p env own) (λi stk. asm_plain_inst i) (λi. F) p d ss` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     `t.sym_base.as_pc = LENGTH pre + m` by metis_tac[] >>
     `m = 0 \/ m = 1 \/ m = 2 \/ m = 3` by decide_tac >>
     gvs[Abbr `p`, EL_APPEND_EQN, asm_plain_inst_def, is_data_inst_def]) >>
  `~sym_terminal (sym_steps_own p env own d ss)` by
    (strip_tac >> drule own_terminal_checkpoint >> strip_tac >>
     `a.sym_base.as_pc = LENGTH pre + i` by metis_tac[] >>
     `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
     gvs[Abbr `p`, EL_APPEND_EQN, sym_step_own_eq, sym_step_push_label, sym_terminal_def,
         sym_step_def, sym_step_op_def, sym_set_stack_def, sym_jumps_not_terminal]) >>
  `sym_prefix_all (sym_steps_own q env own) (λi stk. asm_plain_inst i) (λi. F) q 3 ss` by
    (mp_tac (Q.INST [`chunk` |-> `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`,
       `post` |-> `AsmLabel x :: rest`] plain_chunk_prefix_last_jump) >>
     simp[Abbr `q`, asm_plain_inst_def, is_data_inst_def]) >>
  `sym_steps_own p env own d ss = sym_steps p env d ss` by simp[] >>
  qexists_tac `d` >> BETA_TAC >>
  Cases_on `sym_steps p env d ss` >>
  fs[sym_terminal_def, Abbr `p`, Abbr `q`] >>
  TRY (qexists_tac `0` >> simp[] >> rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC, decide_tac] >> NO_TAC) >>
  qexists_tac `e` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
  TRY (rpt gen_tac >> strip_tac >> `m < 3` by decide_tac >>
    qpat_assum `!m t. m < 3 /\ _ ==> _` (qspecl_then [`m`, `t`] mp_tac) >>
    simp[] >> NO_TAC) >>
  metis_tac[]
QED

Finalise inefficient_window_within_own

Theorem optimize_inefficient_jumps_within_own:
  asm_within_own p (FST (optimize_inefficient_jumps p))
Proof
  BETA_TAC >> strip_tac >>
  mp_tac (Q.SPEC `asm_within_own` inefficient_jumps_prefix_walk) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans] >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]`,
       `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`,
       `post` |-> `AsmLabel x :: rest`] asm_splice_window_within_own) >>
     (impl_tac >-
       (conj_tac
        >- (simp[asm_splice_ok_def, asm_label_refs_def, is_data_inst_def,
                  asm_inst_size_def] >> rw[] >> EVAL_TAC) >>
        simp[inefficient_window_within_own])) >>
     BETA_TAC >> simp[])) >>
  disch_then (qspec_then `p` mp_tac) >> BETA_TAC >> simp[]
QED
