(* Step-bounded splice transport over fixed installed code bytes. *)
Theory asmSpliceWithinOwn
Ancestors
  asmSpliceWithin asmOwnSpliceStep asmSpliceOwn asmOwnLabels asmSymPcOwn
  asmSplice asmSymOwnCode asmSymSemWithin asmSymSem asmSymPc asmWf
  finalizerContract list

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
