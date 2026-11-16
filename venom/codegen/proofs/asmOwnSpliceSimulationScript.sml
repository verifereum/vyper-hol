(* Fuel simulation for own-code splices. Finite execution is supplied by
   its equations, so this theory does not depend on asmSpliceOwn. *)
Theory asmOwnSpliceSimulation
Ancestors
  asmSplice asmSymPc finalizerContractOwn finalizerContract asmSymOwnCode asmSymSem

Theorem own_run_zero[local]:
  sym_run_own p env own 0 ss = SymError "out of fuel"
Proof
  simp[Once sym_run_own_def]
QED

Theorem own_run_steps_ok[local]:
  (!ss. srcSteps 0 ss = SymOK ss) /\
  (!n ss. srcSteps (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK a => srcSteps n a | r => r) ==>
  !j fuel ss a. srcSteps j ss = SymOK a ==>
    sym_run_own p env own (j + fuel) ss = sym_run_own p env own fuel a
Proof
  strip_tac >> Induct >> simp[] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >>
  simp[Once sym_run_own_def, arithmeticTheory.ADD_CLAUSES] >>
  first_x_assum drule >> simp[]
QED

Theorem own_run_steps_stop[local]:
  (!ss. srcSteps 0 ss = SymOK ss) /\
  (!n ss. srcSteps (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK a => srcSteps n a | r => r) ==>
  !j fuel ss. (!a. srcSteps j ss <> SymOK a) /\ j <= fuel ==>
    sym_run_own p env own fuel ss = srcSteps j ss
Proof
  strip_tac >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >> gvs[] >>
  simp[Once sym_run_own_def] >> rw[] >> gvs[] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem own_run_terminal_steps[local]:
  (!ss. srcSteps 0 ss = SymOK ss) /\
  (!n ss. srcSteps (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK a => srcSteps n a | r => r) ==>
  !j fuel ss. sym_terminal (sym_run_own p env own fuel ss) ==>
    (!a. srcSteps j ss = SymOK a ==>
      j < fuel /\ sym_run_own p env own fuel ss =
        sym_run_own p env own (fuel - j) a) /\
    ((!a. srcSteps j ss <> SymOK a) ==>
      sym_run_own p env own fuel ss = srcSteps j ss)
Proof
  strip_tac >>
  `!j fuel ss a. srcSteps j ss = SymOK a ==>
    sym_run_own p env own (j + fuel) ss = sym_run_own p env own fuel a`
    by (ho_match_mp_tac own_run_steps_ok >> simp[]) >>
  `!j fuel ss. (!a. srcSteps j ss <> SymOK a) /\ j <= fuel ==>
    sym_run_own p env own fuel ss = srcSteps j ss`
    by (ho_match_mp_tac own_run_steps_stop >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `j < fuel`
      >- (first_x_assum drule >> disch_then (qspec_then `fuel - j` mp_tac) >>
          simp[]) >>
      first_x_assum drule >> disch_then (qspec_then `0` mp_tac) >>
      simp[own_run_zero] >> strip_tac >>
      `fuel <= j` by decide_tac >>
      drule_then (qspecl_then [`p`, `env`, `own`, `ss`] strip_assume_tac)
        sym_run_own_less_fuel >> gvs[sym_terminal_def]) >>
  Cases_on `j <= fuel` >- (first_x_assum irule >> simp[]) >>
  `fuel <= j` by decide_tac >>
  drule_then (qspecl_then [`p`, `env`, `own`, `ss`] strip_assume_tac)
    sym_run_own_less_fuel >> gvs[sym_terminal_def] >>
  first_x_assum irule >> simp[]
QED

Theorem own_steps_invariant[local]:
  (!ss. srcSteps 0 ss = SymOK ss) /\
  (!n ss. srcSteps (SUC n) ss =
    if ss.sym_base.as_pc >= LENGTH p then SymError "pc out of bounds"
    else case sym_step_own p env own (EL ss.sym_base.as_pc p) ss of
      SymOK a => srcSteps n a | r => r) /\
  (!ss inst a. state_inv ss /\ MEM inst p /\
    sym_step_own p env own inst ss = SymOK a ==> state_inv a) ==>
  !j ss a. state_inv ss /\ srcSteps j ss = SymOK a ==> state_inv a
Proof
  strip_tac >> Induct >> simp[] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `!ss inst a. _` irule >>
  goal_assum (drule_at Any) >> simp[listTheory.EL_MEM]
QED

(* The finite-step equations and the invariant form the entire interface.
   In particular no target label invariant, or positive target chunk, is
   assumed. The sole decreasing measure is source fuel. *)
Theorem splice_run_terminal_own_by_steps:
  asm_splice_ok pat repl /\
  (!ss. srcSteps 0 ss = SymOK ss) /\
  (!j ss. srcSteps (SUC j) ss =
    if ss.sym_base.as_pc >= LENGTH (pfx ++ pat ++ sfx)
    then SymError "pc out of bounds"
    else case sym_step_own (pfx ++ pat ++ sfx) env own
      (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss of
      SymOK a => srcSteps j a | r => r) /\
  (!ss. dstSteps 0 ss = SymOK ss) /\
  (!j ss. dstSteps (SUC j) ss =
    if ss.sym_base.as_pc >= LENGTH (pfx ++ repl ++ sfx)
    then SymError "pc out of bounds"
    else case sym_step_own (pfx ++ repl ++ sfx) env own
      (EL ss.sym_base.as_pc (pfx ++ repl ++ sfx)) ss of
      SymOK a => dstSteps j a | r => r) /\
  (!ss inst a. state_inv ss /\ MEM inst (pfx ++ pat ++ sfx) /\
    sym_step_own (pfx ++ pat ++ sfx) env own inst ss = SymOK a ==>
    state_inv a) /\
  (!ss inst a. state_inv ss /\
    (ss.sym_base.as_pc < LENGTH pfx \/
     LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
    sym_step_own (pfx ++ pat ++ sfx) env own inst ss = SymOK a ==>
    (a.sym_base.as_pc <= LENGTH pfx \/
     LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
    sym_step_own (pfx ++ repl ++ sfx) env own inst
      (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        ss.sym_base.as_pc) ss) =
      SymOK (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
        a.sym_base.as_pc) a)) /\
  (!ss inst. state_inv ss /\
    sym_terminal (sym_step_own (pfx ++ pat ++ sfx) env own inst ss) ==>
    sym_result_rel (sym_step_own (pfx ++ pat ++ sfx) env own inst ss)
      (sym_step_own (pfx ++ repl ++ sfx) env own inst
        (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
          ss.sym_base.as_pc) ss))) /\
  (!ss. state_inv ss /\ ss.sym_base.as_pc = LENGTH pfx ==>
    ?j j'. 0 < j /\
      (!a. srcSteps j ss = SymOK a ==>
        (a.sym_base.as_pc <= LENGTH pfx \/
         LENGTH pfx + LENGTH pat <= a.sym_base.as_pc) /\
        dstSteps j' ss = SymOK (sym_with_pc
          (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
            a.sym_base.as_pc) a)) /\
      (sym_terminal (srcSteps j ss) ==>
        sym_result_rel (srcSteps j ss) (dstSteps j' ss))) ==>
  !fuel ss. state_inv ss /\
    (ss.sym_base.as_pc <= LENGTH pfx \/
     LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc) /\
    sym_terminal (sym_run_own (pfx ++ pat ++ sfx) env own fuel ss) ==>
    ?fuel'. sym_result_rel (sym_run_own (pfx ++ pat ++ sfx) env own fuel ss)
      (sym_run_own (pfx ++ repl ++ sfx) env own fuel'
        (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
          ss.sym_base.as_pc) ss))
Proof
  strip_tac >>
  `!j fuel ss a. dstSteps j ss = SymOK a ==>
    sym_run_own (pfx ++ repl ++ sfx) env own (j + fuel) ss =
    sym_run_own (pfx ++ repl ++ sfx) env own fuel a`
    by (ho_match_mp_tac own_run_steps_ok >> simp[]) >>
  `!j fuel ss. (!a. dstSteps j ss <> SymOK a) /\ j <= fuel ==>
    sym_run_own (pfx ++ repl ++ sfx) env own fuel ss = dstSteps j ss`
    by (ho_match_mp_tac own_run_steps_stop >> simp[]) >>
  `!j fuel ss. sym_terminal (sym_run_own (pfx ++ pat ++ sfx) env own fuel ss) ==>
    (!a. srcSteps j ss = SymOK a ==> j < fuel /\
      sym_run_own (pfx ++ pat ++ sfx) env own fuel ss =
      sym_run_own (pfx ++ pat ++ sfx) env own (fuel - j) a) /\
    ((!a. srcSteps j ss <> SymOK a) ==>
      sym_run_own (pfx ++ pat ++ sfx) env own fuel ss = srcSteps j ss)`
    by (ho_match_mp_tac own_run_terminal_steps >> simp[]) >>
  `!j ss a. state_inv ss /\ srcSteps j ss = SymOK a ==> state_inv a`
    by (ho_match_mp_tac (Q.INST [`p` |-> `pfx ++ pat ++ sfx`,
          `env` |-> `env`, `own` |-> `own`] own_steps_invariant) >> asm_rewrite_tac[]) >>
  completeInduct_on `fuel` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ss.sym_base.as_pc = LENGTH pfx`
  >- suspend "window" >>
  (Q.SUBGOAL_THEN `ss.sym_base.as_pc < LENGTH pfx \/
    LENGTH pfx + LENGTH pat <= ss.sym_base.as_pc` assume_tac
    >- decide_tac) >>
  `pat <> []` by fs[asm_splice_ok_def] >>
  `fuel <> 0 /\ ss.sym_base.as_pc < LENGTH (pfx ++ pat ++ sfx)`
    by (Cases_on `fuel = 0` >>
        fs[Once sym_run_own_def, sym_terminal_def] >>
        Cases_on `ss.sym_base.as_pc >= LENGTH (pfx ++ pat ++ sfx)` >>
        fs[sym_terminal_def]) >>
  drule_all splice_fetch >> strip_tac >>
  first_x_assum (qspec_then `repl` strip_assume_tac) >>
  Cases_on `?a. sym_step_own (pfx ++ pat ++ sfx) env own
    (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss = SymOK a`
  >- suspend "outside_ok" >>
  suspend "outside_terminal"
QED

Resume splice_run_terminal_own_by_steps[window]:
  `sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
     ss.sym_base.as_pc) ss = ss`
    by (simp[splice_pc_def] >>
        qpat_x_assum `ss.sym_base.as_pc = LENGTH pfx`
          (fn th => rewrite_tac[GSYM th]) >> simp[sym_with_pc_def]) >>
  simp[] >>
  qpat_x_assum `!ss. state_inv ss /\ ss.sym_base.as_pc = LENGTH pfx ==> _`
    (qspec_then `ss` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `j` (qx_choose_then `j'` strip_assume_tac)) >>
  qpat_x_assum `!j fuel ss. sym_terminal _ ==> _`
    (qspecl_then [`j`, `fuel`, `ss`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `?a. srcSteps j ss = SymOK a`
  >- suspend "window_ok" >>
  `sym_run_own (pfx ++ pat ++ sfx) env own fuel ss = srcSteps j ss`
    by metis_tac[] >>
  `sym_result_rel (srcSteps j ss) (dstSteps j' ss)` by metis_tac[] >>
  drule sym_result_rel_terminal >> strip_tac >> qexists_tac `j'` >>
  `sym_run_own (pfx ++ repl ++ sfx) env own j' ss = dstSteps j' ss`
    by (first_x_assum irule >> simp[] >>
        Cases_on `dstSteps j' ss` >> gvs[sym_terminal_def]) >> simp[]
QED

Resume splice_run_terminal_own_by_steps[window_ok]:
  qpat_x_assum `?a. _` (qx_choose_then `a` assume_tac) >>
  `j < fuel /\ sym_run_own (pfx ++ pat ++ sfx) env own fuel ss =
    sym_run_own (pfx ++ pat ++ sfx) env own (fuel - j) a` by metis_tac[] >>
  `dstSteps j' ss = SymOK (sym_with_pc
    (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a)`
    by metis_tac[] >>
  `state_inv a` by metis_tac[] >>
  qpat_x_assum `!m. m < fuel ==> _` (qspec_then `fuel - j` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `a` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choose_then `f` assume_tac) >> qexists_tac `j' + f` >>
  qpat_x_assum `!j fuel ss a. dstSteps j ss = SymOK a ==> _`
    (qspecl_then [`j'`, `f`, `ss`] mp_tac) >> simp[] >> metis_tac[]
QED

Resume splice_run_terminal_own_by_steps[outside_ok]:
  qpat_x_assum `?a. _` (qx_choose_then `a` assume_tac) >>
  qpat_assum `!ss inst a. state_inv ss /\ (_ \/ _) /\ _ ==> _`
    (qspecl_then [`ss`, `EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)`, `a`] mp_tac) >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `state_inv a`
    by (qpat_x_assum `!ss inst a. state_inv ss /\ MEM inst _ /\ _ ==> _` irule >>
        goal_assum (drule_at Any) >> simp[listTheory.EL_MEM]) >>
  `sym_run_own (pfx ++ pat ++ sfx) env own fuel ss =
    sym_run_own (pfx ++ pat ++ sfx) env own (fuel - 1) a`
    by (gnvs[listTheory.LENGTH_APPEND] >> simp[Once sym_run_own_def]) >>
  qpat_x_assum `!m. m < fuel ==> _` (qspec_then `fuel - 1` mp_tac) >>
  impl_tac >- decide_tac >> disch_then (qspec_then `a` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qx_choose_then `f` assume_tac) >> qexists_tac `SUC f` >>
  `sym_run_own (pfx ++ repl ++ sfx) env own (SUC f)
     (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       ss.sym_base.as_pc) ss) =
   sym_run_own (pfx ++ repl ++ sfx) env own f
     (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
       a.sym_base.as_pc) a)`
    by (gnvs[sym_with_pc_def, listTheory.LENGTH_APPEND] >>
        simp[Once sym_run_own_def]) >> metis_tac[]
QED

Resume splice_run_terminal_own_by_steps[outside_terminal]:
  qpat_x_assum `!ss inst. state_inv ss /\ sym_terminal _ ==> _` mp_tac >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> strip_tac >>
  `sym_run_own (pfx ++ pat ++ sfx) env own fuel ss =
     sym_step_own (pfx ++ pat ++ sfx) env own
       (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss`
    by (gnvs[listTheory.LENGTH_APPEND] >> simp[Once sym_run_own_def] >>
        Cases_on `sym_step_own (pfx ++ pat ++ sfx) env own
          (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss` >> gvs[]) >>
  `sym_terminal (sym_step_own (pfx ++ pat ++ sfx) env own
     (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)) ss)` by metis_tac[] >>
  qpat_x_assum `!ss inst. state_inv ss /\ sym_terminal _ ==> _`
    (qspecl_then [`ss`, `EL ss.sym_base.as_pc (pfx ++ pat ++ sfx)`] mp_tac) >>
  simp[] >> strip_tac >> drule sym_result_rel_terminal >> strip_tac >>
  qexists_tac `1` >>
  Cases_on `sym_step_own (pfx ++ repl ++ sfx) env own
    (EL ss.sym_base.as_pc (pfx ++ pat ++ sfx))
    (sym_with_pc (splice_pc (LENGTH pfx) (LENGTH pat) (LENGTH repl)
      ss.sym_base.as_pc) ss)` >>
  gvs[sym_terminal_def, Once sym_run_own_def, sym_with_pc_def,
      listTheory.LENGTH_APPEND] >> simp[Once sym_run_own_def]
QED

Finalise splice_run_terminal_own_by_steps
