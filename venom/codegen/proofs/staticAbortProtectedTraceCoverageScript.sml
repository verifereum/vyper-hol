Theory staticAbortProtectedTraceCoverage
Ancestors
  staticAbortProtectedStepControl codegenSymRel asmSplice asmSymSem
  asmSymPc asmOptimizer asmSem list

Theorem protected_prefix_window_entry:
  !n b c s ss.
  s.as_pc=0 /\ b<=c /\ b<LENGTH p /\
  (!j. b<j /\ j<=c ==> j<LENGTH p /\ ~asm_reachable_marker (EL j p)) /\
  sym_steps p env n (sym_init s)=SymOK ss /\ ss.sym_base.as_pc=c
  ==> c-b<=n /\ ?before.
    sym_steps p env (n-(c-b)) (sym_init s)=SymOK before /\
    before.sym_base.as_pc=b /\ sym_steps p env (c-b) before=SymOK ss
Proof
  Induct_on `n`
  >- (simp[sym_steps_def, sym_init_def] >> rpt strip_tac >>
      gvs[] >> simp[sym_steps_def]) >>
  rpt gen_tac >> disch_then strip_assume_tac >>
  Cases_on `b = c`
  >- (gvs[] >> simp[sym_steps_def]) >>
  qpat_x_assum `sym_steps _ _ (SUC n) _ = _` mp_tac >>
  rewrite_tac[arithmeticTheory.ADD1, sym_steps_add] >>
  Cases_on `sym_steps p env n (sym_init s)` >> simp[] >>
  rename1 `sym_steps p env n (sym_init s) = SymOK mid` >>
  rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >>
  simp[AllCaseEqs()] >>
  strip_tac >>
  drule protected_sym_step_control >> strip_tac
  >- (first_x_assum
        (qspecl_then [`b`, `mid.sym_base.as_pc`, `s`, `mid`] mp_tac) >>
      (impl_tac >- simp[]) >>
      strip_tac >>
      `c - b = (mid.sym_base.as_pc - b) + 1` by decide_tac >>
      `b + (n + 1) - c = n - (mid.sym_base.as_pc - b)` by decide_tac >>
      conj_tac >- decide_tac >>
      qexists_tac `before` >> conj_tac
      >- (qpat_x_assum `b + (n + 1) - c = _`
            (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `c - b = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[sym_steps_add] >>
      pure_asm_rewrite_tac[] >>
      rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >> simp[]) >>
  gvs[] >>
  qpat_x_assum `!j. b < j /\ j <= ss.sym_base.as_pc ==> _`
    (qspec_then `ss.sym_base.as_pc` mp_tac) >>
  simp[asm_reachable_marker_def]
QED

Theorem protected_prefix_excludes_dead_run:
  !n s ss.
  p=pre++[term]++dead++tail /\ asm_terminal_op term /\
  EVERY (\i. ~asm_reachable_marker i) dead /\ s.as_pc=0 /\
  sym_steps p env n (sym_init s)=SymOK ss
  ==> ~(LENGTH pre+1<=ss.sym_base.as_pc /\
        ss.sym_base.as_pc<LENGTH pre+1+LENGTH dead)
Proof
  Induct_on `n`
  >- (simp[sym_steps_def, sym_init_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `sym_steps _ _ (SUC n) _ = _` mp_tac >>
  rewrite_tac[arithmeticTheory.ADD1, sym_steps_add] >>
  Cases_on `sym_steps p env n (sym_init s)` >> simp[] >>
  rename1 `sym_steps p env n (sym_init s) = SymOK mid` >>
  Cases_on `mid.sym_base.as_pc >= LENGTH p`
  >- (rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >> gvs[]) >>
  rewrite_tac[arithmeticTheory.ONE, sym_steps_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  first_x_assum (qspecl_then [`s`, `mid`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  drule protected_sym_step_control >> strip_tac
  >- (`mid.sym_base.as_pc = LENGTH pre` by decide_tac >>
      `EL mid.sym_base.as_pc (pre++[term]++dead++tail) = term`
        by simp[EL_APPEND_EQN] >>
      gvs[]) >>
  qpat_x_assum `EL _ _ = AsmLabel l` mp_tac >>
  simp[EL_APPEND_EQN] >> strip_tac >>
  qpat_x_assum `EVERY _ dead` mp_tac >>
  rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `ss.sym_base.as_pc - (LENGTH pre + 1)` mp_tac) >>
  simp[] >> gvs[asm_reachable_marker_def]
QED
