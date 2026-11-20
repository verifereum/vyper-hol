(*
 * The step-bounded local obligation of a single-site splice.
 *
 * asm_window_refines_within is asm_window_refines with a step bound: from
 * the window's start, p' takes at most twice p's steps there, within the
 * same bounds (sym_run_within, sym_within_ok). The bound shares the
 * window's step counts j and j' with the rest, so it is stated with them,
 * not on its own. asm_window_refines stays as it is.
 *
 * TOP-LEVEL:
 *   sym_steps_ok               — n steps that P allows and Q doesn't stop at
 *   asm_window_refines_within  — the step-bounded local obligation
 *)

Theory asmSpliceWithin
Ancestors
  asmRefinesWithin finalizerContract asmWf list
  asmSplice asmSymSemWithin asmSymPc asmSymSem

(* Each of the first n steps from ss runs an instruction that P allows,
   with its stack, and that Q doesn't stop at. *)
Definition sym_steps_ok_def:
  (sym_steps_ok P Q p env 0 ss ⇔ T) ∧
  (sym_steps_ok P Q p env (SUC n) ss ⇔
     ss.sym_base.as_pc < LENGTH p ∧
     ¬Q (EL ss.sym_base.as_pc p) ∧
     P (EL ss.sym_base.as_pc p) ss.sym_stack ∧
     case sym_step p env (EL ss.sym_base.as_pc p) ss of
       SymOK ss' => sym_steps_ok P Q p env n ss'
     | _ => T)
End

(* From the window's start, j > 0 steps of p and j' steps of p' either
   leave the window at corresponding PCs in the same state, or end in
   related terminal results. A run of p that errs or misuses a label
   there constrains nothing. And p' takes at most twice p's steps there,
   within the same bounds: a bounded run of p from the window's start is
   matched by one of p' with twice the steps, or it passes the window's j
   steps, which Q doesn't stop at, and p''s j' steps keep P and Q. *)
Definition asm_window_refines_within_def:
  asm_window_refines_within pfx pat repl sfx ⇔
    asm_static_wf (pfx ++ pat ++ sfx) ⇒
    ∀env ss.
      ss.sym_base.as_pc = LENGTH pfx ∧ ss.sym_base.as_stack = [] ⇒
      ∃j j'.
        0 < j ∧ j' ≤ 2 * j ∧
        (∀a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a ⇒
             (a.sym_base.as_pc ≤ LENGTH pfx ∨
              LENGTH pfx + LENGTH pat ≤ a.sym_base.as_pc) ∧
             sym_steps (pfx ++ repl ++ sfx) env j' ss =
               SymOK (sym_with_pc
                        (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
                           a.sym_base.as_pc) a)) ∧
        (sym_terminal (sym_steps (pfx ++ pat ++ sfx) env j ss) ⇒
         sym_result_rel (sym_steps (pfx ++ pat ++ sfx) env j ss)
           (sym_steps (pfx ++ repl ++ sfx) env j' ss)) ∧
        ∀P Q k.
          sym_within_ok P Q ∧
          sym_run_within P Q (pfx ++ pat ++ sfx) env k ss ⇒
          sym_run_within P Q (pfx ++ repl ++ sfx) env (2 * k) ss ∨
          ∃a. sym_steps (pfx ++ pat ++ sfx) env j ss = SymOK a ∧ j ≤ k ∧
              sym_run_within P Q (pfx ++ pat ++ sfx) env (k - j) a ∧
              sym_steps_ok P Q (pfx ++ repl ++ sfx) env j' ss
End

Theorem asm_window_refines_of_within:
  asm_window_refines_within pfx pat repl sfx ⇒ asm_window_refines pfx pat repl sfx
Proof
  simp[asm_window_refines_def, asm_window_refines_within_def] >>
  metis_tac[]
QED

(* n allowed steps to a, then a bounded run from a. *)
Theorem sym_steps_ok_within:
  ∀n ss a m.
    sym_steps p env n ss = SymOK a ∧ sym_steps_ok P Q p env n ss ∧
    sym_run_within P Q p env m a ⇒
    sym_run_within P Q p env (n + m) ss
Proof
  Induct >> simp[sym_steps_def, sym_steps_ok_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[arithmeticTheory.ADD_CLAUSES, sym_run_within_def]
QED

(* n allowed steps to a terminal result are a bounded run. *)
Theorem sym_steps_ok_terminal:
  ∀n ss.
    sym_terminal (sym_steps p env n ss) ∧ sym_steps_ok P Q p env n ss ⇒
    sym_run_within P Q p env n ss
Proof
  Induct >> simp[sym_steps_def, sym_steps_ok_def, sym_terminal_def] >>
  rpt gen_tac >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >>
  rw[sym_run_within_def] >> gvs[sym_terminal_def]
QED

(* A bounded run through n steps that Q doesn't stop at: P allows each of
   them, and the run from where they lead is bounded by what is left. *)
Theorem sym_run_within_steps:
  ∀n ss a k.
    sym_run_within P Q p env k ss ∧ sym_steps p env n ss = SymOK a ∧
    sym_steps_ok (λi stk. T) Q p env n ss ⇒
    n ≤ k ∧ sym_run_within P Q p env (k - n) a ∧
    sym_steps_ok P Q p env n ss
Proof
  Induct >> simp[sym_steps_def, sym_steps_ok_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[sym_run_within_def] >>
  first_x_assum drule_all >> simp[]
QED

(* One step of sym_steps_ok, for a step count given as a numeral. *)
Theorem sym_steps_ok_pos:
  0 < n ⇒
  (sym_steps_ok P Q p env n ss ⇔
     ss.sym_base.as_pc < LENGTH p ∧
     ¬Q (EL ss.sym_base.as_pc p) ∧
     P (EL ss.sym_base.as_pc p) ss.sym_stack ∧
     case sym_step p env (EL ss.sym_base.as_pc p) ss of
       SymOK ss' => sym_steps_ok P Q p env (n - 1) ss'
     | _ => T)
Proof
  Cases_on `n` >> simp[sym_steps_ok_def]
QED

Theorem sym_steps_ok_mono:
  ∀n ss.
    (∀i stk. P1 i stk ∧ ¬Q1 i ⇒ P2 i stk ∧ ¬Q2 i) ∧
    sym_steps_ok P1 Q1 p env n ss ⇒ sym_steps_ok P2 Q2 p env n ss
Proof
  Induct >> simp[sym_steps_ok_def] >> rpt gen_tac >> strip_tac >>
  CASE_TAC >> gvs[] >> metis_tac[]
QED

(* A window's steps that run only plain instructions: a bounded run of p
   passes them, and p''s plain steps keep the bounds. *)
Theorem window_within_plain:
  sym_within_ok P Q ∧ sym_run_within P Q p env k ss ∧
  sym_steps p env j ss = SymOK a ∧
  sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p env j ss ∧
  sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p' env j' ss ⇒
  j ≤ k ∧ sym_run_within P Q p env (k - j) a ∧
  sym_steps_ok P Q p' env j' ss
Proof
  strip_tac >> fs[sym_within_ok_def] >>
  `sym_steps_ok (λi stk. T) Q p env j ss`
    by (irule sym_steps_ok_mono >> first_x_assum (irule_at Any) >>
        simp[]) >>
  drule_all sym_run_within_steps >> strip_tac >> simp[] >>
  irule sym_steps_ok_mono >> first_x_assum (irule_at Any) >> simp[]
QED

(* The bounded conjunct of a window whose steps, in both programs, run
   only plain instructions to a state a of the original. *)
Theorem window_bounded_plain:
  sym_steps p env j ss = SymOK b ∧
  sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p env j ss ∧
  sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p' env j' ss ∧
  sym_within_ok P Q ∧ sym_run_within P Q p env k ss ⇒
  sym_run_within P Q p' env (2 * k) ss ∨
  ∃a. sym_steps p env j ss = SymOK a ∧ j ≤ k ∧
      sym_run_within P Q p env (k - j) a ∧
      sym_steps_ok P Q p' env j' ss
Proof
  rpt strip_tac >> disj2_tac >> simp[] >>
  metis_tac[window_within_plain]
QED

Theorem sym_steps_ok_one:
  sym_steps_ok P Q p env 1 ss ⇔
    ss.sym_base.as_pc < LENGTH p ∧ ¬Q (EL ss.sym_base.as_pc p) ∧
    P (EL ss.sym_base.as_pc p) ss.sym_stack
Proof
  simp[sym_steps_ok_pos, sym_steps_ok_def] >> CASE_TAC >> simp[]
QED

(* A first step that leaves no state to go on from, taken the same way by
   a second program, bounds its run too. *)
Theorem within_same_halting_step:
  sym_run_within P Q p env k ss ∧ 0 < k' ∧
  ss.sym_base.as_pc < LENGTH q ∧
  EL ss.sym_base.as_pc q = EL ss.sym_base.as_pc p ∧
  (∀a. sym_step p env (EL ss.sym_base.as_pc p) ss ≠ SymOK a) ∧
  sym_step q env (EL ss.sym_base.as_pc p) ss =
    sym_step p env (EL ss.sym_base.as_pc p) ss ⇒
  sym_run_within P Q q env k' ss
Proof
  Cases_on `k` >> Cases_on `k'` >> simp[sym_run_within_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[]
QED

(* A bounded run never errs before Q stops it. *)
Theorem sym_run_within_steps_error:
  ∀n ss k.
    sym_run_within P Q p env k ss ∧
    sym_steps_ok (λi stk. T) Q p env n ss ⇒
    ∀e. sym_steps p env n ss ≠ SymError e ∧ sym_steps p env n ss ≠ SymBad e
Proof
  Induct >> simp[sym_steps_def, sym_steps_ok_def] >> rpt gen_tac >>
  strip_tac >> Cases_on `k` >> gvs[sym_run_within_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  metis_tac[]
QED

(* The bounded conjunct of a window whose steps, in both programs, run only
   plain instructions: a bounded run can't err there, so it gets through
   the window, or halts in it, and then p' halts within two steps. *)
Theorem window_bounded_cases:
  sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p env j ss ∧
  (∀b. sym_steps p env j ss = SymOK b ⇒
       sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p' env j' ss) ∧
  (sym_terminal (sym_steps p env j ss) ⇒
   sym_terminal (sym_steps p' env j' ss) ∧ j' ≤ 2 ∧
   sym_steps_ok (λi stk. asm_plain_inst i) (λi. F) p' env j' ss) ∧
  sym_within_ok P Q ∧ sym_run_within P Q p env k ss ⇒
  sym_run_within P Q p' env (2 * k) ss ∨
  ∃a. sym_steps p env j ss = SymOK a ∧ j ≤ k ∧
      sym_run_within P Q p env (k - j) a ∧
      sym_steps_ok P Q p' env j' ss
Proof
  strip_tac >>
  `0 < k` by (Cases_on `k` >> gvs[sym_run_within_def]) >>
  Cases_on `sym_steps p env j ss` >> gvs[sym_terminal_def]
  >- (drule_all window_bounded_plain >> simp[]) >>
  `sym_steps_ok (λi stk. T) Q p env j ss`
    by (irule sym_steps_ok_mono >> first_x_assum (irule_at Any) >>
        gvs[sym_within_ok_def]) >>
  drule_all sym_run_within_steps_error >> simp[] >>
  irule sym_run_within_mono >> qexists_tac `j'` >> simp[] >>
  irule sym_steps_ok_terminal >> simp[] >>
  irule sym_steps_ok_mono >> first_x_assum (irule_at Any) >>
  gvs[sym_within_ok_def]
QED

Theorem within_stop[local]:
  ss.sym_base.as_pc < LENGTH p /\ Q (EL ss.sym_base.as_pc p) ==>
  sym_run_within P Q p env (SUC n) ss
Proof
  simp[sym_run_within_def]
QED

Theorem within_terminal_step[local]:
  ss.sym_base.as_pc < LENGTH p /\ P (EL ss.sym_base.as_pc p) ss.sym_stack /\
  sym_terminal (sym_step p env (EL ss.sym_base.as_pc p) ss) ==>
  sym_run_within P Q p env (SUC n) ss
Proof
  simp[sym_run_within_def] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >>
  simp[sym_terminal_def]
QED

(* A prefix guard written on run states. This allows both step models to
   use the splice certificates' existing window checkpoint equations. *)
Overload sym_prefix_all = ``\(runf:num -> sym_state -> sym_result) P Q p n s.
  !m t. m < n /\ runf m s = SymOK t ==>
    t.sym_base.as_pc < LENGTH p /\
    ~Q (EL t.sym_base.as_pc p) /\
    P (EL t.sym_base.as_pc p) t.sym_stack``

Overload sym_prefix_driver = ``\stepf runf p.
  (!ss. runf 0 ss = SymOK ss) /\
  (!n ss. runf (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else case stepf (EL ss.sym_base.as_pc p) ss of
      SymOK next => runf n next
    | r => r)``

Theorem sym_prefix_all_suc:
  sym_prefix_driver stepf runf p ==>
  (sym_prefix_all runf P Q p (SUC n) ss <=>
   ss.sym_base.as_pc < LENGTH p /\ ~Q (EL ss.sym_base.as_pc p) /\
   P (EL ss.sym_base.as_pc p) ss.sym_stack /\
   case stepf (EL ss.sym_base.as_pc p) ss of
     SymOK next => sym_prefix_all runf P Q p n next
   | _ => T)
Proof
  BETA_TAC >> strip_tac >> eq_tac
  >- (strip_tac >> first_assum (qspecl_then [`0`, `ss`] mp_tac) >> simp[] >>
      strip_tac >> simp[] >> CASE_TAC >> simp[] >>
      rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`SUC m`, `t`] mp_tac) >> simp[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `m` >> gvs[] >>
  Cases_on `stepf (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  metis_tac[]
QED

Theorem sym_steps_ok_as_prefix_all:
  !n ss.
    sym_steps_ok P Q p env n ss <=>
    sym_prefix_all (sym_steps p env) P Q p n ss
Proof
  Induct >- simp[sym_steps_ok_def] >> gen_tac >>
  mp_tac (Q.INST [`stepf` |-> `sym_step p env`, `runf` |-> `sym_steps p env`]
    (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_suc)) >>
  (impl_tac >- simp[sym_steps_def]) >>
  disch_then (fn th => simp_tac bool_ss [th, sym_steps_ok_def]) >>
  CASE_TAC >> simp[]
QED

Theorem sym_prefix_all_append_within:
  sym_prefix_driver stepf runf p ==>
  !n ss next k.
    runf n ss = SymOK next /\ sym_prefix_all runf P Q p n ss /\
    sym_run_within_for stepf P Q p k next ==>
    sym_run_within_for stepf P Q p (n + k) ss
Proof
  disch_then assume_tac >> Induct >- fs[] >>
  rpt gen_tac >>
  mp_tac sym_prefix_all_suc >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ONCE_REWRITE_TAC o single) >>
  simp[arithmeticTheory.ADD_CLAUSES, sym_run_within_for_def] >>
  strip_tac >> Cases_on `stepf (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  metis_tac[]
QED

Theorem sym_prefix_all_terminal_within:
  sym_prefix_driver stepf runf p ==>
  !n ss.
    sym_terminal (runf n ss) /\ sym_prefix_all runf P Q p n ss ==>
    sym_run_within_for stepf P Q p n ss
Proof
  disch_then assume_tac >> Induct >- fs[sym_terminal_def] >>
  gen_tac >> mp_tac sym_prefix_all_suc >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ONCE_REWRITE_TAC o single) >>
  simp[sym_run_within_for_def] >>
  strip_tac >> Cases_on `stepf (EL ss.sym_base.as_pc p) ss` >>
  gvs[sym_terminal_def] >> metis_tac[]
QED

Theorem sym_prefix_all_split_within:
  sym_prefix_driver stepf runf p ==>
  !n ss next k.
    sym_run_within_for stepf P Q p k ss /\ runf n ss = SymOK next /\
    sym_prefix_all runf (\i stk. T) Q p n ss ==>
    n <= k /\ sym_run_within_for stepf P Q p (k - n) next /\
    sym_prefix_all runf P Q p n ss
Proof
  disch_then assume_tac >> Induct >- fs[] >>
  rpt gen_tac >>
  mp_tac (Q.INST [`P` |-> `\(i:'a) (stk:sval list). T`] sym_prefix_all_suc) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ONCE_REWRITE_TAC o single) >>
  mp_tac sym_prefix_all_suc >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ONCE_REWRITE_TAC o single) >>
  Cases_on `k` >> simp[sym_run_within_for_def] >> strip_tac >>
  Cases_on `stepf (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  first_x_assum (qspecl_then [`s`, `next`, `n'`] mp_tac) >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem sym_prefix_all_cong:
  (!m. m < n ==> runf m ss = runf' m ss) ==>
  (sym_prefix_all runf P Q p n ss <=> sym_prefix_all runf' P Q p n ss)
Proof
  BETA_TAC >> metis_tac[]
QED

Theorem sym_run_within_for_no_error:
  sym_prefix_driver stepf runf p ==>
  !n ss k.
    sym_run_within_for stepf P Q p k ss /\
    sym_prefix_all runf (\i stk. T) Q p n ss ==>
    !e. runf n ss <> SymError e /\ runf n ss <> SymBad e
Proof
  disch_then assume_tac >> Induct >- fs[] >>
  rpt gen_tac >>
  mp_tac (Q.INST [`P` |-> `\(i:'a) (stk:sval list). T`] sym_prefix_all_suc) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ONCE_REWRITE_TAC o single) >>
  Cases_on `k` >> simp[sym_run_within_for_def] >> strip_tac >>
  Cases_on `stepf (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  first_x_assum (qspecl_then [`s`, `n'`] mp_tac) >> simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

(* The bounded walk only needs a way to replay a window and simulate one
   instruction outside it. The symbolic step functions can read fixed bytes. *)
Theorem splice_run_within_for:
  !shift. shift = (\s. sym_with_pc
    (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) s.sym_base.as_pc) s) ==>
  pat <> [] /\ sym_prefix_driver target_step target_run (pre ++ repl ++ post) /\
  (!s k. allowed s /\ s.sym_base.as_pc = LENGTH pre /\
     sym_run_within_for source_step P Q (pre ++ pat ++ post) k s ==>
     sym_run_within_for target_step P Q (pre ++ repl ++ post) (2 * k) s \/
     ?j j' a. 0 < j /\ j <= k /\ j' <= 2 * j /\ allowed a /\
       (a.sym_base.as_pc <= LENGTH pre \/
        LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
       sym_run_within_for source_step P Q (pre ++ pat ++ post) (k - j) a /\
       target_run j' s = SymOK (shift a) /\
       sym_prefix_all target_run P Q (pre ++ repl ++ post) j' s) /\
  (!s inst a. allowed s /\
     (s.sym_base.as_pc < LENGTH pre \/ LENGTH pre + LENGTH pat <= s.sym_base.as_pc) /\
     s.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
     inst = EL s.sym_base.as_pc (pre ++ pat ++ post) /\ source_step inst s = SymOK a ==>
     allowed a /\
     (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
     target_step inst (shift s) = SymOK (shift a)) /\
  (!s inst. allowed s /\
     (s.sym_base.as_pc < LENGTH pre \/ LENGTH pre + LENGTH pat <= s.sym_base.as_pc) /\
     s.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
     inst = EL s.sym_base.as_pc (pre ++ pat ++ post) /\ sym_terminal (source_step inst s) ==>
     sym_terminal (target_step inst (shift s))) ==>
  !k ss. allowed ss /\
    (ss.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= ss.sym_base.as_pc) /\
    sym_run_within_for source_step P Q (pre ++ pat ++ post) k ss ==>
    sym_run_within_for target_step P Q (pre ++ repl ++ post) (2 * k) (shift ss)
Proof
  gen_tac >> disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  strip_tac >> completeInduct_on `k` >> gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ss.sym_base.as_pc = LENGTH pre`
  >- suspend "window"
  >> suspend "outside"
QED

Resume splice_run_within_for[window]:
  `shift ss = ss` by
    (simp[Abbr `shift`, splice_pc_def] >>
     qpat_assum `ss.sym_base.as_pc = LENGTH pre`
       (fn th => rewrite_tac[GSYM th]) >> simp[sym_with_pc_def]) >>
  qpat_x_assum `!s k. allowed s /\ _ ==> _`
    (qspecl_then [`ss`, `k`] mp_tac) >> simp[] >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`j`, `j'`, `a`] (map_every assume_tac o CONJUNCTS))) >>
  simp[] >>
  `sym_run_within_for target_step P Q (pre ++ repl ++ post) (2 * (k - j)) (shift a)` by
    (qpat_x_assum `!m. m < k ==> _` (qspec_then `k - j` mp_tac) >>
     impl_tac >- decide_tac >> disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  irule sym_run_within_for_mono >>
  qexists_tac `j' + 2 * (k - j)` >> conj_tac >- decide_tac >>
  mp_tac (Q.INST [`stepf` |-> `target_step`, `runf` |-> `target_run`,
    `p` |-> `pre ++ repl ++ post`] sym_prefix_all_append_within) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`j'`, `ss`, `shift a`, `2 * (k - j)`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Resume splice_run_within_for[outside]:
  (Q.SUBGOAL_THEN `ss.sym_base.as_pc < LENGTH pre \/
     LENGTH pre + LENGTH pat <= ss.sym_base.as_pc` assume_tac
    >- decide_tac) >>
  Cases_on `k` >> fs[sym_run_within_for_def] >>
  `ss.sym_base.as_pc < LENGTH (pre ++ pat ++ post)` by fs[] >>
  qabbrev_tac `i = EL ss.sym_base.as_pc (pre ++ pat ++ post)` >>
  `(shift ss).sym_base.as_pc < LENGTH (pre ++ repl ++ post) /\
   EL (shift ss).sym_base.as_pc (pre ++ repl ++ post) = i` by
    (mp_tac (Q.INST [`i` |-> `ss.sym_base.as_pc`, `pfx` |-> `pre`, `sfx` |-> `post`]
       splice_fetch) >> simp[Abbr `shift`, Abbr `i`, sym_with_pc_def]) >>
  `(shift ss).sym_stack = ss.sym_stack` by simp[Abbr `shift`, sym_with_pc_def] >>
  `2 * SUC n = SUC (2 * n + 1)` by decide_tac >>
  pop_assum SUBST1_TAC >> simp[sym_run_within_for_def] >>
  Cases_on `Q i` >> fs[] >>
  Cases_on `?a. source_step i ss = SymOK a` >>
  FIRST
  [qpat_x_assum `?a. source_step i ss = SymOK a` (qx_choose_then `a` assume_tac) >>
   `allowed a /\
    (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
    target_step i (shift ss) = SymOK (shift a)` by
     (qpat_x_assum `!s a. _ ==> allowed a /\ _ /\ target_step _ (shift s) = SymOK (shift a)`
        (qspecl_then [`ss`, `a`] mp_tac) >> fs[Abbr `i`]) >>
   fs[] >>
   irule sym_run_within_for_mono >> qexists_tac `2 * n` >> simp[] >>
   qpat_x_assum `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[] >>
   disch_then (qspec_then `a` mp_tac) >> simp[],
   `sym_terminal (source_step i ss)` by
     (Cases_on `source_step i ss` >> gvs[sym_terminal_def]) >>
   `sym_terminal (target_step i (shift ss))` by
     (qpat_x_assum `!s. _ ==> sym_terminal (target_step _ (shift s))`
        (qspec_then `ss` mp_tac) >> fs[Abbr `i`]) >>
   Cases_on `target_step i (shift ss)` >> gvs[sym_terminal_def]]
QED

Finalise splice_run_within_for

(* The bounded counterpart: a bounded run of p from outside the window, or
   its start, is matched by one of p' with at most twice the steps. *)
Theorem splice_run_within[local]:
  asm_splice_ok pat repl /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pfx ++ pat ++ sfx))) /\
  asm_window_refines_within pfx pat repl sfx /\ asm_static_wf (pfx ++ pat ++ sfx) /\
  sym_within_ok P Q ==>
  !k env ss.
    ss.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) ss /\
    (ss.sym_base.as_pc <= LENGTH pfx \/
      LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
    sym_run_within P Q (pfx ++ pat ++ sfx) env k ss ==>
    sym_run_within P Q (pfx ++ repl ++ sfx) env (2 * k)
      (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc) ss)
Proof
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `pat <> []` by fs[asm_splice_ok_def] >>
  qabbrev_tac `shift = \s. sym_with_pc
    (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) s.sym_base.as_pc) s` >>
  mp_tac (Q.INST [
    `pre` |-> `pfx`, `post` |-> `sfx`,
    `source_step` |-> `sym_step (pfx ++ pat ++ sfx) env`,
    `target_step` |-> `sym_step (pfx ++ repl ++ sfx) env`,
    `target_run` |-> `sym_steps (pfx ++ repl ++ sfx) env`,
    `allowed` |-> `\u. u.sym_base.as_stack = [] /\
      sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) u`]
    (INST_TYPE [alpha |-> ``:asm_inst``] splice_run_within_for)) >>
  disch_then (qspec_then `shift` mp_tac) >>
  (impl_tac >- simp[Abbr `shift`]) >> BETA_TAC >>
  (impl_tac >- suspend "hypotheses") >>
  disch_then (qspecl_then [`k`, `ss`] mp_tac) >>
  simp[GSYM sym_run_within_for_sym_step, Abbr `shift`]
QED

Resume splice_run_within[hypotheses]:
  simp[sym_steps_def, GSYM sym_run_within_for_sym_step,
       GSYM sym_steps_ok_as_prefix_all] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `asm_window_refines_within _ _ _ _` mp_tac >>
      simp[asm_window_refines_within_def] >>
      disch_then (qspecl_then [`env`, `s`] mp_tac) >> simp[] >>
      disch_then (qx_choosel_then [`j`, `j'`] strip_assume_tac) >>
      qpat_x_assum `!P Q k. sym_within_ok P Q /\ _ ==> _`
        (qspecl_then [`P`, `Q`, `k'`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >> disj2_tac >>
      qexistsl_tac [`j`, `j'`, `a`] >> simp[Abbr `shift`] >>
      metis_tac[sym_steps_base_stack, sym_steps_labels_in])
  >- (rpt gen_tac >> strip_tac >> simp[Abbr `shift`] >>
      rename1 `sym_step _ _ (EL _ _) now = SymOK next` >>
      `MEM (EL now.sym_base.as_pc (pfx ++ pat ++ sfx)) (pfx ++ pat ++ sfx)`
        by simp[listTheory.EL_MEM] >>
      mp_tac (Q.INST [`ss` |-> `now`, `a` |-> `next`,
        `inst` |-> `EL now.sym_base.as_pc (pfx ++ pat ++ sfx)`]
        splice_inst_step_ok) >> simp[] >>
      metis_tac[sym_step_base_stack, sym_step_labels_in]) >>
  rpt gen_tac >> strip_tac >> simp[Abbr `shift`] >>
  metis_tac[splice_inst_step_terminal, sym_result_rel_terminal]
QED

Finalise splice_run_within

Theorem asm_splice_window_refines_both:
  asm_splice_ok pat repl ∧
  (∀l. MEM (AsmLabel l) pat ⇒ ¬MEM l (asm_label_refs (pfx ++ pat ++ sfx))) ∧
  asm_window_refines_within pfx pat repl sfx ⇒
  asm_refines_both (pfx ++ pat ++ sfx) (pfx ++ repl ++ sfx)
Proof
  strip_tac >> simp[relationTheory.RINTER] >>
  conj_tac >- metis_tac[asm_splice_window_refines, asm_window_refines_of_within] >>
  simp[asm_refines_within_def] >> strip_tac >>
  qexists_tac `2` >> rpt strip_tac >>
  drule_at (Pat `sym_run_within _ _ _ _ _ _`) splice_run_within >>
  simp[sym_init_def, splice_pc_def, sym_with_pc_def,
       sym_state_labels_in_def, listTheory.MEM_MAP]
QED

Theorem asm_refines_both_cons:
  (∀pfx. asm_refines_both (pfx ++ rest) (pfx ++ out)) ⇒
  ∀pfx. asm_refines_both (pfx ++ x :: rest) (pfx ++ x :: out)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `pfx ++ [x]` mp_tac) >>
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]
QED
