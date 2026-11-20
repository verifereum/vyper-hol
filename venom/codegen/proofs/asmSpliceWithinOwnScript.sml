(* Step-bounded splice transport over fixed installed code bytes. *)
Theory asmSpliceWithinOwn
Ancestors
  asmRefinesWithin asmSpliceWithin asmOwnSpliceStep asmSpliceOwn asmOwnLabels asmSymPcOwn
  asmSplice asmSymOwnCode asmSymSemWithin asmSymSem asmSymPc asmWf
  finalizerContract list rich_list

(* The own-code window certificate constrains only the visited steps.
   Outside the window both programs read the same installed bytes. *)
Overload own_window_within = ``\pre pat repl post.
  !env own ss P Q k.
    ss.sym_base.as_pc = LENGTH pre /\ ss.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) ss /\
    sym_within_ok P Q /\
    sym_run_within_for (sym_step_own (pre ++ pat ++ post) env own) P Q
      (pre ++ pat ++ post) k ss ==>
    sym_run_within_for (sym_step_own (pre ++ repl ++ post) env own) P Q
      (pre ++ repl ++ post) (2 * k) ss \/
    ?j j' a. 0 < j /\ j <= k /\ j' <= 2 * j /\
      (a.sym_base.as_pc <= LENGTH pre \/
       LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
      sym_steps_own (pre ++ pat ++ post) env own j ss = SymOK a /\
      sym_run_within_for (sym_step_own (pre ++ pat ++ post) env own) P Q
        (pre ++ pat ++ post) (k - j) a /\
      sym_steps_own (pre ++ repl ++ post) env own j' ss =
        SymOK (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
          a.sym_base.as_pc) a) /\
      sym_prefix_all (sym_steps_own (pre ++ repl ++ post) env own) P Q
        (pre ++ repl ++ post) j' ss``

Overload asm_within_own = ``\p q. asm_static_wf p ==>
  asm_static_wf q /\
  ?c. !P Q env own s k. sym_within_ok P Q /\
    sym_run_within_for (sym_step_own p env own) P Q p k (sym_init s) ==>
    sym_run_within_for (sym_step_own q env own) P Q q (c * k) (sym_init s)``

Theorem asm_within_own_refl:
  asm_within_own p p
Proof
  BETA_TAC >> strip_tac >> simp[] >> qexists_tac `1` >> simp[]
QED

Theorem asm_within_own_trans:
  asm_within_own p q /\ asm_within_own q r ==> asm_within_own p r
Proof
  BETA_TAC >> strip_tac >> strip_tac >>
  qpat_assum `asm_static_wf p ==> _` drule >> strip_tac >>
  qpat_assum `asm_static_wf q ==> _` drule >> strip_tac >> simp[] >>
  qmatch_asmsub_rename_tac `sym_run_within_for _ _ _ q (ca * _) _` >>
  qmatch_asmsub_rename_tac `sym_run_within_for _ _ _ r (cb * _) _` >>
  qexists_tac `cb * ca` >> rpt gen_tac >> strip_tac >>
  `cb * ca * k = cb * (ca * k)` by simp[] >> pop_assum SUBST1_TAC >>
  metis_tac[]
QED

Theorem asm_splice_window_within_own:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  (asm_static_wf (pre ++ pat ++ post) ==> own_window_within pre pat repl post) ==>
  asm_within_own (pre ++ pat ++ post) (pre ++ repl ++ post)
Proof
  strip_tac >> BETA_TAC >> strip_tac >>
  `pat <> []` by fs[asm_splice_ok_def] >>
  `asm_static_wf (pre ++ repl ++ post)` by
    (`!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ repl ++ post))` by
       (gvs[asm_splice_ok_def, label_refs_append] >> metis_tac[]) >>
     drule_all asm_splice_static_wf >> simp[]) >>
  simp[] >> qexists_tac `2` >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `shift = \s. sym_with_pc
    (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) s.sym_base.as_pc) s` >>
  `shift (sym_init s) = sym_init s` by
    simp[Abbr `shift`, sym_init_def, splice_pc_def, sym_with_pc_def] >>
  mp_tac (Q.INST [
    `source_step` |-> `sym_step_own (pre ++ pat ++ post) env own`,
    `target_step` |-> `sym_step_own (pre ++ repl ++ post) env own`,
    `target_run` |-> `sym_steps_own (pre ++ repl ++ post) env own`,
    `allowed` |-> `\u. u.sym_base.as_stack = [] /\
      sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u`]
    (INST_TYPE [alpha |-> ``:asm_inst``] splice_run_within_for)) >>
  disch_then (qspec_then `shift` mp_tac) >>
  (impl_tac >- simp[Abbr `shift`]) >> BETA_TAC >>
  (impl_tac >- suspend "hypotheses") >>
  disch_then (qspecl_then [`k`, `sym_init s`] mp_tac) >>
  simp[sym_init_def, sym_state_labels_in_def, MEM_MAP]
QED

Resume asm_splice_window_within_own[hypotheses]:
  simp[sym_steps_own_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `asm_static_wf _ ==> own_window_within _ _ _ _` mp_tac >>
      simp[] >> disch_then (qspecl_then [`env`, `own`, `s'`, `P`, `Q`, `k'`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      disj2_tac >> qexistsl_tac [`j`, `j'`, `a`] >> simp[] >>
      metis_tac[sym_steps_own_preserves_splice_invariant])
  >- (rpt gen_tac >> strip_tac >> simp[Abbr `shift`] >>
      rename1 `sym_step_own _ _ _ (EL _ _) now = SymOK next` >>
      `MEM (EL now.sym_base.as_pc (pre ++ pat ++ post)) (pre ++ pat ++ post)`
        by simp[EL_MEM] >>
      mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `post`,
        `ss` |-> `now`, `a` |-> `next`,
        `inst` |-> `EL now.sym_base.as_pc (pre ++ pat ++ post)`]
        splice_inst_step_own_ok) >> simp[] >>
      metis_tac[sym_step_own_base_stack, sym_step_own_labels_in]) >>
  rpt gen_tac >> strip_tac >> simp[Abbr `shift`] >>
  metis_tac[splice_inst_step_own_terminal, sym_result_rel_terminal]
QED

Finalise asm_splice_window_within_own

Theorem plain_prefix_guards:
  sym_within_ok P Q /\
  sym_prefix_all runf (λi stk. asm_plain_inst i) (λi. F) p n ss ==>
  sym_prefix_all runf P Q p n ss /\ sym_prefix_all runf (λi stk. T) Q p n ss
Proof
  BETA_TAC >> fs[sym_within_ok_def] >> strip_tac >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

(* Plain instructions cannot stop a bounded run at Q. If a plain window
   passes its source steps, the replacement passes its own steps. *)
Theorem window_bounded_cases_for:
  sym_prefix_driver source_step source_run p /\
  sym_prefix_driver target_step target_run q /\
  sym_prefix_all source_run (λi stk. asm_plain_inst i) (λi. F) p j ss /\
  sym_prefix_all target_run (λi stk. asm_plain_inst i) (λi. F) q j' ss /\
  (sym_terminal (source_run j ss) ==> sym_terminal (target_run j' ss) /\ j' <= 2) /\
  sym_within_ok P Q /\ sym_run_within_for source_step P Q p k ss ==>
  sym_run_within_for target_step P Q q (2 * k) ss \/
  ?a. source_run j ss = SymOK a /\ j <= k /\
      sym_run_within_for source_step P Q p (k - j) a /\
      sym_prefix_all target_run P Q q j' ss
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < k` by (Cases_on `k` >> fs[sym_run_within_for_def]) >>
  `sym_prefix_all source_run (λi stk. T) Q p j ss` by
    (mp_tac (Q.INST [`runf` |-> `source_run`, `n` |-> `j`,
        `P` |-> `P`, `Q` |-> `Q`] plain_prefix_guards) >>
     BETA_TAC >> (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `sym_prefix_all target_run P Q q j' ss` by
    (mp_tac (Q.INST [`runf` |-> `target_run`, `p` |-> `q`,
        `n` |-> `j'`, `P` |-> `P`, `Q` |-> `Q`] plain_prefix_guards) >>
     BETA_TAC >> (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `!e. source_run j ss <> SymError e /\ source_run j ss <> SymBad e` by
    (mp_tac (Q.INST [`stepf` |-> `source_step`, `runf` |-> `source_run`,
        `P` |-> `P`, `Q` |-> `Q`, `p` |-> `p`]
       (INST_TYPE [alpha |-> ``:asm_inst``] sym_run_within_for_no_error)) >>
     (impl_tac >- fs[]) >>
     disch_then (qspecl_then [`j`, `ss`, `k`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  Cases_on `source_run j ss` >> gvs[sym_terminal_def]
  >- (rename1 `source_run j ss = SymOK next` >>
   disj2_tac >>
   mp_tac (Q.INST [`stepf` |-> `source_step`, `runf` |-> `source_run`,
       `P` |-> `P`, `Q` |-> `Q`, `p` |-> `p`]
     (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_split_within)) >>
   (impl_tac >- fs[]) >>
   disch_then (qspecl_then [`j`, `ss`, `next`, `k`] mp_tac) >>
   (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >>
   disch_then (map_every assume_tac o CONJUNCTS) >>
   rpt conj_tac >> first_assum ACCEPT_TAC) >>
   `j' <= 2 * k` by decide_tac >>
   irule sym_run_within_for_mono >> qexists_tac `j'` >> simp[] >>
   mp_tac (Q.INST [`stepf` |-> `target_step`, `runf` |-> `target_run`,
     `P` |-> `P`, `Q` |-> `Q`, `p` |-> `q`]
     (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_terminal_within)) >>
   (impl_tac >- fs[]) >>
   disch_then (qspecl_then [`j'`, `ss`] mp_tac) >>
   (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
   disch_then ACCEPT_TAC
QED

(* A straight window may halt early, but any executed instruction is plain. *)
Theorem own_window_plain_within:
  (!env own ss. ss.sym_base.as_pc = LENGTH pre /\ ss.sym_base.as_stack = [] ==>
    ?j j'. 0 < j /\ j' <= 2 * j /\
      own_window_results pre pat repl post env own ss j j' /\
      sym_prefix_all (sym_steps_own (pre ++ pat ++ post) env own)
        (λi stk. asm_plain_inst i) (λi. F) (pre ++ pat ++ post) j ss /\
      sym_prefix_all (sym_steps_own (pre ++ repl ++ post) env own)
        (λi stk. asm_plain_inst i) (λi. F) (pre ++ repl ++ post) j' ss /\
      (sym_terminal (sym_steps_own (pre ++ pat ++ post) env own j ss) ==> j' <= 2)) ==>
  own_window_within pre pat repl post
Proof
  disch_then assume_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `p = pre ++ pat ++ post` >>
  qabbrev_tac `q = pre ++ repl ++ post` >>
  qpat_x_assum `!env own ss. _ ==> _`
    (qspecl_then [`env`, `own`, `ss`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`j`, `j'`] (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`source_step` |-> `sym_step_own p env own`,
    `source_run` |-> `sym_steps_own p env own`, `p` |-> `p`,
    `target_step` |-> `sym_step_own q env own`,
    `target_run` |-> `sym_steps_own q env own`, `q` |-> `q`,
    `j` |-> `j`, `j'` |-> `j'`, `P` |-> `P`, `Q` |-> `Q`,
    `k` |-> `k`, `ss` |-> `ss`] window_bounded_cases_for) >>
  (impl_tac >-
    (simp[sym_steps_own_def] >> BETA_TAC >>
     fs[Abbr `p`, Abbr `q`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     metis_tac[sym_result_rel_terminal])) >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac) >>
  simp[] >> disj2_tac >> qexistsl_tac [`j`, `j'`, `a`] >>
  fs[Abbr `p`, Abbr `q`] >> metis_tac[]
QED

Theorem sym_steps_own_straight_prefix[local]:
  !n ss.
    (!i. i < n ==>
      ss.sym_base.as_pc + i < LENGTH p /\
      asm_plain_inst (EL (ss.sym_base.as_pc + i) p) /\
      (SUC i < n ==>
       EL (ss.sym_base.as_pc + i) p <> AsmOp "JUMP" /\
       EL (ss.sym_base.as_pc + i) p <> AsmOp "JUMPI")) ==>
    sym_prefix_all (sym_steps_own p env own) (λi stk. asm_plain_inst i)
      (λi. F) p n ss
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc < LENGTH p /\ asm_plain_inst (EL ss.sym_base.as_pc p) /\
    (0 < n ==> EL ss.sym_base.as_pc p <> AsmOp "JUMP" /\
               EL ss.sym_base.as_pc p <> AsmOp "JUMPI")` by
    (qpat_assum `!i. i < SUC n ==> _`
       (qspec_then `0` (ACCEPT_TAC o SIMP_RULE (srw_ss()) []))) >>
  mp_tac (Q.INST [`stepf` |-> `sym_step_own p env own`,
    `runf` |-> `sym_steps_own p env own`, `p` |-> `p`,
    `P` |-> `λi stk. asm_plain_inst i`, `Q` |-> `λi. F`]
    (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_suc)) >>
  (impl_tac >- simp[sym_steps_own_def]) >>
  disch_then (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >>
  simp[] >> rename1 `_ = SymOK next` >>
  Cases_on `n = 0` >- (BETA_TAC >> simp[]) >>
  `next.sym_base.as_pc = ss.sym_base.as_pc + 1`
    by (drule_at (Pos last) sym_step_own_pc_next >> simp[]) >>
  qpat_x_assum `!ss. _ ==> sym_prefix_all _ _ _ _ _ _`
    (qspec_then `next` mp_tac) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `!i. i < SUC n ==> _` (qspec_then `SUC i`
      (mp_tac o SIMP_RULE (srw_ss()) [DECIDE ``pc + SUC i = (pc + 1) + i``])) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >> pure_asm_rewrite_tac [] >> simp[])) >>
  disch_then (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
QED

Overload asm_straight_plain = ``λi. asm_plain_inst i /\
  i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI"``

Theorem plain_chunk_prefix_last_jump:
  ss.sym_base.as_pc = LENGTH pre /\ EVERY asm_plain_inst chunk /\
  EVERY (λi. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI")
    (TAKE (LENGTH chunk - 1) chunk) ==>
  sym_prefix_all (sym_steps_own (pre ++ chunk ++ post) env own)
    (λi stk. asm_plain_inst i) (λi. F) (pre ++ chunk ++ post) (LENGTH chunk) ss
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`LENGTH (chunk:asm_inst list)`, `ss`]
    (Q.INST [`p` |-> `pre ++ chunk ++ post`] sym_steps_own_straight_prefix)) >>
  (impl_tac >-
    (gen_tac >> strip_tac >>
     `LENGTH pre + i < LENGTH pre + LENGTH chunk` by decide_tac >>
     `EL (LENGTH pre + i) (pre ++ chunk ++ post) = EL i chunk`
       by simp[EL_APPEND_EQN] >>
     `LENGTH pre + i < LENGTH (pre ++ chunk ++ post)` by (simp[] >> decide_tac) >>
     `asm_plain_inst (EL i chunk)` by fs[EVERY_EL] >>
     pure_asm_rewrite_tac[] >> simp[] >> strip_tac >>
     `i < LENGTH chunk - 1` by decide_tac >>
     qpat_assum `EVERY _ (TAKE _ _)` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[LENGTH_TAKE_EQ, EL_TAKE] >>
     strip_tac >> simp[])) >>
  disch_then ACCEPT_TAC
QED

Theorem plain_chunk_prefix:
  ss.sym_base.as_pc = LENGTH pre /\ EVERY asm_straight_plain chunk ==>
  sym_prefix_all (sym_steps_own (pre ++ chunk ++ post) env own)
    (λi stk. asm_plain_inst i) (λi. F) (pre ++ chunk ++ post) (LENGTH chunk) ss
Proof
  strip_tac >>
  mp_tac plain_chunk_prefix_last_jump >>
  (impl_tac >- (fs[EVERY_MEM] >> metis_tac[MEM_TAKE])) >>
  disch_then ACCEPT_TAC
QED

Theorem own_window_straight_within:
  pat <> [] /\ LENGTH repl <= 2 /\ LENGTH repl <= 2 * LENGTH pat /\
  EVERY asm_straight_plain pat /\ EVERY asm_straight_plain repl /\
  (!env own ss. ss.sym_base.as_pc = LENGTH pre /\ ss.sym_base.as_stack = [] ==>
     own_window_results pre pat repl post env own ss (LENGTH pat) (LENGTH repl)) ==>
  own_window_within pre pat repl post
Proof
  strip_tac >>
  mp_tac own_window_plain_within >>
  (impl_tac >- suspend "certificate") >> disch_then ACCEPT_TAC
QED

Resume own_window_straight_within[certificate]:
  rpt gen_tac >> strip_tac >>
  `0 < LENGTH pat` by (Cases_on `pat` >> fs[]) >>
  `own_window_results pre pat repl post env own ss (LENGTH pat) (LENGTH repl)` by
    (first_x_assum (qspecl_then [`env`, `own`, `ss`] mp_tac) >> simp[]) >>
  `sym_prefix_all (sym_steps_own (pre ++ pat ++ post) env own)
    (λi stk. asm_plain_inst i) (λi. F) (pre ++ pat ++ post) (LENGTH pat) ss` by
    (mp_tac (Q.INST [`chunk` |-> `pat`] plain_chunk_prefix) >> simp[]) >>
  `sym_prefix_all (sym_steps_own (pre ++ repl ++ post) env own)
    (λi stk. asm_plain_inst i) (λi. F) (pre ++ repl ++ post) (LENGTH repl) ss` by
    (mp_tac (Q.INST [`chunk` |-> `repl`] plain_chunk_prefix) >> simp[]) >>
  qexistsl_tac [`LENGTH pat`, `LENGTH repl`] >>
  fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise own_window_straight_within
