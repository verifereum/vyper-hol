Theory staticAbortOptMergeIszeroSync
Ancestors
  asmSymPcOwn staticAbortProtectedStepControl staticAbortProtectedTraceCoverage codegenSymRel asmSplice asmSymPc asmSymSem
  asmOptimizer asmSem arithmetic list

Theorem sym_init_prefix_base_stack_mode:
  !n ss. sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss ==>
         ss.sym_base.as_stack = []
Proof
  Induct_on `n`
  >- simp[sym_steps_mode_zero, sym_init_def] >>
  gen_tac >> rewrite_tac[ADD1, sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own p env own n (sym_init s)` >> simp[] >>
  rewrite_tac[sym_steps_mode_ok_one] >>
  Cases_on `allow_own` >>
  PURE_REWRITE_TAC [COND_CLAUSES] >>
  metis_tac[sym_step_base_stack, sym_step_own_base_stack]
QED

Theorem sym_init_prefix_base_stack:
  !n ss. sym_steps p env n (sym_init s) = SymOK ss ==>
         ss.sym_base.as_stack = []
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`] sym_init_prefix_base_stack_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED

Theorem merge_iszero_synchronized_replay_mode:
  !b. b = LENGTH pre ==>
  !m. m = LENGTH pat ==>
  !r. r = splice_pc b m (LENGTH repl) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\ 2 <= m /\
  (!i. b < i /\ i < b+m ==> ~asm_reachable_marker (EL i p)) /\
  (!i. b <= i /\ i+1 < b+m ==>
       EL i p <> AsmOp "JUMP" /\ EL i p <> AsmOp "JUMPI") /\
  (!u v. (u.sym_base.as_pc < b \/ b+m <= u.sym_base.as_pc) /\
     sym_steps_mode allow_own p env own 1 u = SymOK v ==>
     sym_steps_mode allow_own q env own 1 (sym_with_pc (r u.sym_base.as_pc) u) =
       SymOK (sym_with_pc (r v.sym_base.as_pc) v)) /\
  (!u v. u.sym_base.as_pc = b /\ u.sym_base.as_stack = [] /\
     sym_steps_mode allow_own p env own m u = SymOK v ==>
     ?k. sym_steps_mode allow_own q env own k u = SymOK (sym_with_pc (r v.sym_base.as_pc) v)) /\
  s.as_pc = 0 ==>
  !n ss. sym_steps_mode allow_own p env own n (sym_init s) = SymOK ss /\
         ~(b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+m) ==>
         ?j. sym_steps_mode allow_own q env own j (sym_init s) =
               SymOK (sym_with_pc (r ss.sym_base.as_pc) ss)
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >> strip_tac >>
  completeInduct_on `n` >> Cases_on `n`
  >- (simp[sym_steps_mode_zero, sym_init_def, splice_pc_def, sym_with_pc_def] >>
      rpt strip_tac >> qexists_tac `0` >>
      gvs[sym_steps_mode_zero, sym_with_pc_def, splice_pc_def]) >>
  qx_gen_tac `ss` >> strip_tac >>
  qabbrev_tac `b = LENGTH pre` >> qabbrev_tac `m = LENGTH pat` >>
  qabbrev_tac `r = splice_pc b m (LENGTH repl)` >>
  qpat_x_assum `sym_steps_mode allow_own p env own (SUC _) _ = _` mp_tac >>
  rewrite_tac[ADD1, sym_steps_mode_add] >>
  Cases_on `sym_steps_mode allow_own p env own n' (sym_init s)` >> simp[] >>
  rename1 `sym_steps_mode allow_own p env own n' (sym_init s) = SymOK mid` >>
  strip_tac >>
  Q_TAC ASM_CASES_TAC `mid.sym_base.as_pc < b \/ b+m <= mid.sym_base.as_pc`
  >- suspend "outside" >>
  suspend "window"
QED

Resume merge_iszero_synchronized_replay_mode[outside]:
  `~(b < mid.sym_base.as_pc /\ mid.sym_base.as_pc < b+m)` by decide_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _`
    (qspec_then `n'` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!u v. (_ \/ _) /\ sym_steps_mode allow_own p env own 1 u = _ ==> _`
    (qspecl_then [`mid`, `ss`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `j+1` >> simp[sym_steps_mode_add]
QED

Resume merge_iszero_synchronized_replay_mode[window]:
  `b <= mid.sym_base.as_pc /\ mid.sym_base.as_pc < b+m` by decide_tac >>
  `mid.sym_base.as_pc + 1 = b+m` by (
    CCONTR_TAC >>
    `mid.sym_base.as_pc + 1 < b+m` by decide_tac >>
    `EL mid.sym_base.as_pc p <> AsmOp "JUMP" /\
     EL mid.sym_base.as_pc p <> AsmOp "JUMPI"` by metis_tac[] >>
    `(if allow_own then sym_step_own p env own (EL mid.sym_base.as_pc p) mid
      else sym_step p env (EL mid.sym_base.as_pc p) mid) = SymOK ss` by
      fs[sym_steps_mode_ok_one] >>
    `ss.sym_base.as_pc = mid.sym_base.as_pc + 1`
      by metis_tac[protected_step_pc_next] >> decide_tac) >>
  `mid.sym_base.as_pc - b <= n' /\ ?entry.
     sym_steps_mode allow_own p env own (n'-(mid.sym_base.as_pc-b)) (sym_init s) = SymOK entry /\
     entry.sym_base.as_pc = b /\
     sym_steps_mode allow_own p env own (mid.sym_base.as_pc-b) entry = SymOK mid` by (
    irule protected_prefix_window_entry_mode >>
    `b+m <= LENGTH p` by simp[Abbr `b`, Abbr `m`] >>
    simp[] >> rpt strip_tac >> decide_tac) >>
  `m = (mid.sym_base.as_pc-b)+1` by decide_tac >>
  `sym_steps_mode allow_own p env own m entry = SymOK ss` by (
    qpat_assum `m = _` (once_rewrite_tac o single) >> simp[sym_steps_mode_add]) >>
  `entry.sym_base.as_stack = []` by metis_tac[sym_init_prefix_base_stack_mode] >>
  `r b = b` by (
    qpat_assum `Abbrev (r = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    simp[NoAsms, splice_pc_def]) >>
  `sym_with_pc (r entry.sym_base.as_pc) entry = entry` by (
    qpat_assum `entry.sym_base.as_pc = b` SUBST1_TAC >>
    qpat_assum `r b = b` SUBST1_TAC >>
    qpat_assum `entry.sym_base.as_pc = b` (SUBST1_TAC o SYM) >>
    simp[NoAsms, sym_with_pc_def]) >>
  qpat_x_assum `!h. h < SUC _ ==> _`
    (qspec_then `n'-(mid.sym_base.as_pc-b)` mp_tac) >>
  `n'-(mid.sym_base.as_pc-b) < SUC n'` by decide_tac >>
  disch_then (qspec_then `entry` mp_tac o UNDISCH) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac)) >>
  qpat_x_assum `sym_with_pc (r entry.sym_base.as_pc) entry = entry`
    (pure_rewrite_tac o single) >>
  strip_tac >>
  qpat_x_assum `!u v. u.sym_base.as_pc = b /\ _ ==> _`
    (qspecl_then [`entry`, `ss`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_assum `q = _` (SUBST1_TAC o SYM) >>
  qexists_tac `j+k` >> rewrite_tac[sym_steps_mode_add] >>
  qpat_assum `sym_steps_mode allow_own q env own j (sym_init s) = SymOK entry`
    (pure_rewrite_tac o single) >>
  simp[NoAsms] >> first_assum ACCEPT_TAC
QED

Finalise merge_iszero_synchronized_replay_mode

Theorem merge_iszero_synchronized_replay:
  !b. b = LENGTH pre ==>
  !m. m = LENGTH pat ==>
  !r. r = splice_pc b m (LENGTH repl) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\ 2 <= m /\
  (!i. b < i /\ i < b+m ==> ~asm_reachable_marker (EL i p)) /\
  (!i. b <= i /\ i+1 < b+m ==>
       EL i p <> AsmOp "JUMP" /\ EL i p <> AsmOp "JUMPI") /\
  (!u v. (u.sym_base.as_pc < b \/ b+m <= u.sym_base.as_pc) /\
     sym_steps p env 1 u = SymOK v ==>
     sym_steps q env 1 (sym_with_pc (r u.sym_base.as_pc) u) =
       SymOK (sym_with_pc (r v.sym_base.as_pc) v)) /\
  (!u v. u.sym_base.as_pc = b /\ u.sym_base.as_stack = [] /\
     sym_steps p env m u = SymOK v ==>
     ?k. sym_steps q env k u = SymOK (sym_with_pc (r v.sym_base.as_pc) v)) /\
  s.as_pc = 0 ==>
  !n ss. sym_steps p env n (sym_init s) = SymOK ss /\
         ~(b < ss.sym_base.as_pc /\ ss.sym_base.as_pc < b+m) ==>
         ?j. sym_steps q env j (sym_init s) =
               SymOK (sym_with_pc (r ss.sym_base.as_pc) ss)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`] merge_iszero_synchronized_replay_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
