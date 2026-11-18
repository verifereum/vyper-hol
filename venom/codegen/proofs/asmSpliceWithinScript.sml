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
  strip_tac >> completeInduct_on `k` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ss.sym_base.as_pc = LENGTH pfx`
  >- suspend "window" >>
  (Q.SUBGOAL_THEN `ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc` assume_tac
    >- decide_tac) >>
  `pat <> []` by fs[asm_splice_ok_def] >>
  `?k'. k = SUC k'` by (Cases_on `k` >> fs[sym_run_within_def]) >>
  fs[] >>
  `ss.sym_base.as_pc < LENGTH (pfx ++ pat ++ sfx)`
    by fs[sym_run_within_def] >>
  `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) ss.sym_base.as_pc <
     LENGTH (pfx ++ repl ++ sfx) /\
   EL (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) ss.sym_base.as_pc)
     (pfx ++ repl ++ sfx) = EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)`
    by (irule (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch) >> fs[]) >>
  suspend "outside"
QED

Resume splice_run_within[window]:
  `sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
     ss.sym_base.as_pc) ss = ss`
    by (simp[splice_pc_def] >>
        qpat_x_assum `ss.sym_base.as_pc = LENGTH pfx`
          (fn th => rewrite_tac[GSYM th]) >> simp[sym_with_pc_def]) >>
  simp[] >>
  qpat_x_assum `asm_window_refines_within _ _ _ _` mp_tac >>
  simp[asm_window_refines_within_def] >>
  disch_then (qspecl_then [`env`, `ss`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `j` (qx_choose_then `j'` strip_assume_tac)) >>
  first_x_assum (qspecl_then [`P`, `Q`, `k`] mp_tac) >> simp[] >>
  strip_tac >> simp[] >>
  Q.SUBGOAL_THEN `sym_steps (pfx ++ repl ++ sfx) env j' ss =
     SymOK (sym_with_pc
       (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a) /\
    (a.sym_base.as_pc <= LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= a.sym_base.as_pc)`
    (CONJUNCTS_THEN assume_tac)
  >- (qpat_assum `!a. sym_steps _ _ _ _ = SymOK a ==> _` drule >>
      rpt strip_tac >> simp[] >> decide_tac) >>
  `a.sym_base.as_stack = []` by metis_tac[sym_steps_base_stack] >>
  `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) a`
    by metis_tac[sym_steps_labels_in] >>
  first_x_assum (qspec_then `k - j` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`env`, `a`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all sym_steps_ok_within >> strip_tac >>
  irule sym_run_within_mono >>
  first_x_assum (irule_at Any) >> decide_tac
QED

Resume splice_run_within[outside]:
  markerLib.RESUME_TAC >>
  (
  `2 * SUC k' = SUC (2 * k' + 1)` by decide_tac >> pop_assum SUBST1_TAC >>
  Cases_on `Q (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx))`
  >- (irule within_stop >> fs[sym_with_pc_def]) >>
  `P (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss.sym_stack`
    by (qpat_x_assum `sym_run_within _ _ (pfx ++ pat ++ sfx) _ _ ss` mp_tac >>
        ONCE_REWRITE_TAC [sym_run_within_def] >> simp[]) >>
  Cases_on `?a. sym_step (pfx ++ pat ++ sfx) env
    (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss = SymOK a`
  >- suspend "outside_ok" >>
  `sym_terminal (sym_step (pfx ++ pat ++ sfx) env
     (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss)`
    by (qpat_x_assum `sym_run_within _ _ _ _ _ _` mp_tac >>
        ONCE_REWRITE_TAC [sym_run_within_def] >> simp[] >>
        Cases_on `sym_step (pfx ++ pat ++ sfx) env
          (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss` >>
        gvs[sym_terminal_def]) >>
  drule_all splice_inst_step_terminal >>
  disch_then (qspec_then `splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
    ss.sym_base.as_pc` assume_tac) >>
  drule sym_result_rel_terminal >> strip_tac >>
  irule within_terminal_step >> fs[sym_with_pc_def])
QED

Resume splice_run_within[outside_ok]:
  markerLib.RESUME_TAC >>
  (
  qpat_x_assum `?a. _` (qx_choose_then `a` assume_tac) >>
  Q.SUBGOAL_THEN `ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc` assume_tac
  >- decide_tac >>
  drule_all splice_inst_step_ok >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.sym_base.as_stack = []` by metis_tac[sym_step_base_stack] >>
  `sym_state_labels_in (asm_label_refs (pfx ++ pat ++ sfx)) a`
    by metis_tac[sym_step_labels_in, listTheory.EL_MEM] >>
  `sym_run_within P Q (pfx ++ pat ++ sfx) env k' a`
    by (qpat_x_assum `sym_run_within _ _ (pfx ++ pat ++ sfx) _ _ ss` mp_tac >>
        ONCE_REWRITE_TAC [sym_run_within_def] >> simp[]) >>
  first_x_assum (qspec_then `k'` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`env`, `a`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  irule sym_run_within_mono >>
  qexists_tac `SUC (2 * k')` >> conj_tac >- decide_tac >>
  ONCE_REWRITE_TAC [sym_run_within_def] >> fs[sym_with_pc_def])
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
