Theory staticAbortProtectedFetch
Ancestors
  staticAbortProtectedTraceCoverage asmSymPcOwn asmSymOwnCode codegenSymRel

Theorem protected_mode_fetch_pos:
  0 < n /\ ss.sym_base.as_pc < LENGTH p ==>
  sym_steps_mode allow_own p env own n ss =
    case (if allow_own /\ (EL ss.sym_base.as_pc p = AsmOp "CODESIZE" \/
                            EL ss.sym_base.as_pc p = AsmOp "CODECOPY")
          then sym_step_own p env own (EL ss.sym_base.as_pc p) ss
          else sym_step p env (EL ss.sym_base.as_pc p) ss) of
      SymOK next => sym_steps_mode allow_own p env own (n-1) next
    | r => r
Proof
  simp[LET_THM] >> strip_tac >> drule_all sym_steps_mode_pos >>
  qabbrev_tac `inst = EL ss.sym_base.as_pc p` >>
  Cases_on `allow_own` >> simp[] >>
  Cases_on `inst = AsmOp "CODESIZE" \/ inst = AsmOp "CODECOPY"` >>
  fs[DE_MORGAN_THM, sym_step_own_eq]
QED

Theorem protected_mode_fetch_one:
  sym_steps_mode allow_own p env own 1 ss =
  if LENGTH p <= ss.sym_base.as_pc then SymError "pc out of bounds"
  else
    if allow_own /\ (EL ss.sym_base.as_pc p = AsmOp "CODESIZE" \/
                     EL ss.sym_base.as_pc p = AsmOp "CODECOPY")
    then sym_step_own p env own (EL ss.sym_base.as_pc p) ss
    else sym_step p env (EL ss.sym_base.as_pc p) ss
Proof
  ONCE_REWRITE_TAC [arithmeticTheory.ONE] >>
  PURE_REWRITE_TAC [sym_steps_mode_suc, sym_steps_mode_zero, LET_THM] >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p` >> simp[] >>
  Cases_on `allow_own` >> simp[]
  >- (qabbrev_tac `inst = EL ss.sym_base.as_pc p` >>
      Cases_on `inst = AsmOp "CODESIZE" \/ inst = AsmOp "CODECOPY"` >>
      fs[DE_MORGAN_THM, sym_step_own_eq] >> BasicProvers.CASE_TAC >> simp[]) >>
  BasicProvers.CASE_TAC >> simp[]
QED

Theorem protected_mode_fetch_two:
  sym_steps_mode allow_own p env own 2 ss =
  case sym_steps_mode allow_own p env own 1 ss of
     SymOK next => sym_steps_mode allow_own p env own 1 next
   | res => res
Proof
  PURE_ONCE_REWRITE_TAC [GSYM (EVAL ``1+1:num``)] >>
  PURE_ONCE_REWRITE_TAC [sym_steps_mode_add] >> REFL_TAC
QED

Theorem protected_mode_fetch_three:
  sym_steps_mode allow_own p env own 3 ss =
  case sym_steps_mode allow_own p env own 1 ss of
     SymOK next => sym_steps_mode allow_own p env own 2 next
   | res => res
Proof
  PURE_ONCE_REWRITE_TAC [GSYM (EVAL ``1+2:num``)] >>
  PURE_ONCE_REWRITE_TAC [sym_steps_mode_add] >> REFL_TAC
QED
