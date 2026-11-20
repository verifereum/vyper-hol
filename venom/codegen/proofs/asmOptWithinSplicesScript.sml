(* Bounded own-code runs through the optimizer's local deletions. *)
Theory asmOptWithinSplices
Ancestors
  asmSpliceWithinOwn asmSpliceWithin asmSymSemWithin asmRefinesWithin asmSplice asmSymOwnCode
  asmSymSem asmSymPc asmSymPcOwn asmSpliceOwn asmWf asmSem asmOptimizer list
  asmOptOwnPruneUnreachable asmOptPruneUnreachable asmOptPruneJumps
  asmFinalizerPrefixPruneJumps asmFinalizerPrefixJumpDelete
  asmFinalizerPrefixUnreachable asmFinalizerPrefixUnused

Theorem unused_label_within_own[local]:
  own_window_within pre [AsmLabel l] [] post
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = pre ++ [AsmLabel l] ++ post` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmLabel l` by
    simp[Abbr `p`, EL_APPEND_EQN] >>
  `EL ss.sym_base.as_pc p = AsmLabel l` by metis_tac[] >>
  `P (AsmLabel l) ss.sym_stack /\ ~Q (AsmLabel l)` by
    fs[sym_within_ok_def, asm_plain_inst_def, is_data_inst_def] >>
  qabbrev_tac `a = sym_with_pc (LENGTH pre + 1) ss` >>
  `sym_step_own p env own (AsmLabel l) ss = SymOK a` by
    simp[Abbr `a`, sym_step_own_eq, sym_step_def, sym_lift_def, asm_step_def,
      asm_next_def, sym_with_pc_def, sym_state_component_equality,
      asm_state_component_equality] >>
  `ss with sym_base := (ss.sym_base with as_pc := LENGTH pre) = ss` by
    (qpat_assum `ss.sym_base.as_pc = LENGTH pre`
       (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  Cases_on `k` >> fs[sym_run_within_for_def] >>
  disj2_tac >> qexistsl_tac [`1`, `0`, `a`] >>
  simp[sym_steps_own_one, sym_steps_own_def, Abbr `a`, splice_pc_def,
    sym_with_pc_def] >>
  fs[sym_with_pc_def]
QED

Theorem prune_unused_jumpdests_within_own:
  asm_within_own p (FST (prune_unused_jumpdests p))
Proof
  mp_tac (Q.SPEC `asm_within_own` prune_unused_prefix_walk) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans] >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
       asm_splice_window_within_own) >>
     fs[asm_splice_ok_def, asm_label_refs_def, is_data_inst_def,
       unused_label_within_own])) >>
  disch_then (qspecl_then [`p`, `[]`, `asm_label_refs p`] mp_tac) >>
  simp[prune_unused_jumpdests_def]
QED


Theorem jump_to_next_within_own[local]:
  asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: post) ==>
  own_window_within pre [AsmPushLabel x; AsmOp "JUMP"] [] (AsmLabel x :: post)
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: post` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmPushLabel x /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp "JUMP"` by
    simp[Abbr `p`, EL_APPEND_EQN] >>
  `~Q (AsmPushLabel x) /\ ~Q (AsmOp "JUMP")` by
    fs[sym_within_ok_def, asm_plain_inst_def, is_data_inst_def] >>
  qabbrev_tac `a = sym_with_pc (LENGTH pre + 2) ss` >>
  `sym_steps_own p env own 2 ss = SymOK a` by
    (`sym_steps_own p env own 2 ss = sym_steps p env 2 ss` by
       (simp_tac bool_ss [Abbr `p`] >> irule sym_steps_own_agree_on_chunk >>
        simp[]) >>
     mp_tac (Q.SPECL [`pre`, `x`, `post`, `env`, `ss`] jump_delete_prefix_chunk) >>
     simp[Abbr `p`, Abbr `a`]) >>
  `sym_prefix_all (sym_steps_own p env own) (λi stk. T) Q p 2 ss` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     `m = 0 \/ m = 1` by decide_tac >>
     gvs[sym_steps_own_one, sym_steps_own_def, sym_step_own_eq,
         sym_step_push_label, asm_next_def]) >>
  mp_tac (Q.INST [`stepf` |-> `sym_step_own p env own`,
    `runf` |-> `sym_steps_own p env own`, `P` |-> `P`, `Q` |-> `Q`, `p` |-> `p`]
    (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_split_within)) >>
  (impl_tac >- simp[sym_steps_own_def]) >>
  disch_then (qspecl_then [`2`, `ss`, `a`, `k`] mp_tac) >>
  (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> disj2_tac >> qexistsl_tac [`2`, `0`, `a`] >>
  fs[sym_steps_own_def, Abbr `a`, splice_pc_def, sym_with_pc_def,
       sym_state_component_equality, asm_state_component_equality]
QED

Theorem prune_inefficient_jumps_within_own:
  asm_within_own p (FST (prune_inefficient_jumps p))
Proof
  mp_tac (Q.SPEC `asm_within_own` prune_jumps_prefix_walk) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans] >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
       `repl` |-> `[]`, `post` |-> `AsmLabel x :: rest`]
       asm_splice_window_within_own) >>
     simp[asm_splice_ok_def, asm_label_refs_def, is_data_inst_def,
       symbolResolveTheory.asm_inst_size_def, jump_to_next_within_own])) >>
  disch_then (qspecl_then [`p`, `[]`] mp_tac) >> simp[]
QED


Theorem terminal_within_own[local]:
  asm_terminal_op t /\ ~asm_reachable_marker x ==>
  own_window_within pre [t; x] [t] post
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = pre ++ [t; x] ++ post` >>
  qabbrev_tac `q = pre ++ [t] ++ post` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = t /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = t` by
    simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `t <> AsmOp "CODESIZE" /\ t <> AsmOp "CODECOPY"` by fs[asm_terminal_op_def] >>
  `sym_step_own p env own t ss = sym_step p env t ss /\
   sym_step_own q env own t ss = sym_step q env t ss` by simp[sym_step_own_eq] >>
  `!a. sym_step p env t ss = SymOK a ==>
       sym_step q env t ss =
         SymOK (sym_with_pc (splice_pc (LENGTH pre) 2 1 a.sym_base.as_pc) a) /\
       (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + 2 <= a.sym_base.as_pc)` by
    (mp_tac (Q.INST [`u` |-> `ss`] terminal_prefix_window) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o CONJUNCT2) >>
     `sym_steps p env 1 ss = sym_step p env t ss /\
      sym_steps q env 1 ss = sym_step q env t ss` by
       (simp[sym_steps_pos, sym_steps_def] >>
        Cases_on `sym_step p env t ss` >> Cases_on `sym_step q env t ss` >> simp[]) >>
     qpat_x_assum `Abbrev (p = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_x_assum `Abbrev (q = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[]) >>
  `sym_terminal (sym_step p env t ss) ==>
   sym_step q env t ss = sym_step p env t ss` by
    (strip_tac >>
     `t <> AsmOp "JUMP" /\ t <> AsmOp "JUMPI"` by
       (conj_tac >> strip_tac >> gvs[sym_step_def, sym_step_op_def, sym_jumps_not_terminal]) >>
     `!l. AsmDataHeader l <> x` by
       (rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
     `!l. AsmDataHeader l <> t` by fs[asm_terminal_op_def] >>
     irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  Cases_on `k` >> fs[sym_run_within_for_def] >>
  `2 * SUC n = SUC (2 * n + 1)` by decide_tac >> pop_assum SUBST1_TAC >>
  Cases_on `Q t` >> fs[sym_run_within_for_def] >>
  Cases_on `sym_step p env t ss` >> gvs[sym_terminal_def] >>
  FIRST [disj1_tac >> simp[sym_terminal_def] >> NO_TAC,
    disj2_tac >> qexistsl_tac [`1`, `1`, `s`] >>
    simp[sym_steps_own_one] >> BETA_TAC >> rpt strip_tac >>
    gvs[sym_steps_own_def]]
QED

Theorem prune_unreachable_code_within_own:
  asm_within_own p (FST (prune_unreachable_code p))
Proof
  mp_tac (Q.SPEC `asm_within_own` prune_unreachable_prefix_walk) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans] >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pat` |-> `[t; x]`, `repl` |-> `[t]`]
       asm_splice_window_within_own) >>
     (impl_tac >-
       (conj_tac >- metis_tac[terminal_prefix_splice_ok] >>
        conj_tac
        >- (simp[] >> gen_tac >> strip_tac >> gvs[asm_terminal_op_def, asm_reachable_marker_def]) >>
        simp[terminal_within_own])) >>
     BETA_TAC >> simp[])) >>
  disch_then (qspecl_then [`p`, `F`, `[]`] mp_tac) >>
  simp[prune_unreachable_code_def]
QED
