(* Conditional run simulation for merge_jumpdests with fixed own-code bytes. *)
Theory asmOwnMergeRun
Ancestors
  asmOptMergeJumpdests asmSymPcOwn asmSymOwnCode asmSymSem asmOptimizer
  asmWf asmSem list rich_list

Theorem rename_run_own_under:
  !p i x y env own.
  asm_static_wf p /\ INDEX_OF (AsmLabel x) p = SOME i /\
  (!ss ss' inst.
    rn_rel x y ss ss' /\ ~sym_data_label p env x ==>
    case sym_step_own p env own inst ss of
      SymOK t =>
        (?t'. sym_step_own (MAP (rename_push_label x y) p) env own
                (rename_push_label x y inst) ss' = SymOK t' /\
              rn_rel x y t t') \/
        (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc /\
         !j. INDEX_OF (AsmLabel y) p = SOME j ==>
           ?t'. sym_step_own (MAP (rename_push_label x y) p) env own
                  (rename_push_label x y inst) ss' = SymOK t' /\
                rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t')
    | r => res_rel x y r
             (sym_step_own (MAP (rename_push_label x y) p) env own
               (rename_push_label x y inst) ss')) /\
  (!t fuel. t.sym_base.as_pc = i /\ t.sym_base.as_stack = [] /\
            sym_terminal (sym_run_own p env own fuel t) ==>
            ?j fuel2. INDEX_OF (AsmLabel y) p = SOME j /\ fuel2 < fuel /\
              sym_run_own p env own fuel t =
              sym_run_own p env own fuel2
                (t with sym_base := t.sym_base with as_pc := j)) ==>
  !fuel ss ss'.
    rn_rel x y ss ss' /\ sym_terminal (sym_run_own p env own fuel ss) ==>
    ?fuel'. sym_result_rel (sym_run_own p env own fuel ss)
              (sym_run_own (MAP (rename_push_label x y) p) env own fuel' ss')
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (AsmLabel x) p`
    by metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_SOME_NONE] >>
  `~sym_data_label p env x`
    by (fs[asm_static_wf_def, sym_data_label_def] >> metis_tac[]) >>
  completeInduct_on `fuel` >> rpt strip_tac >>
  `fuel <> 0 /\ ss.sym_base.as_pc < LENGTH p`
    by (spose_not_then strip_assume_tac >>
        qpat_x_assum `sym_terminal _` mp_tac >>
        rw[Once sym_run_own_def, sym_terminal_def] >> gvs[]) >>
  `ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  `!f. sym_run_own (MAP (rename_push_label x y) p) env own (SUC f) ss' =
       case sym_step_own (MAP (rename_push_label x y) p) env own
              (rename_push_label x y (EL ss.sym_base.as_pc p)) ss' of
         SymOK t' => sym_run_own (MAP (rename_push_label x y) p) env own f t'
       | r => r` by simp[Once sym_run_own_def, EL_MAP] >>
  qpat_x_assum `!ss ss' inst. _`
    (qspecl_then [`ss`, `ss'`, `EL ss.sym_base.as_pc p`] mp_tac) >>
  simp[] >>
  qpat_x_assum `sym_terminal _` mp_tac >>
  simp[Once sym_run_own_def] >>
  Cases_on `sym_step_own p env own (EL ss.sym_base.as_pc p) ss` >>
  simp[res_rel_def, sym_terminal_def] >> rpt (disch_then assume_tac)
  >- (
    rename1 `sym_step_own p env own _ ss = SymOK t` >>
    `sym_run_own p env own fuel ss = sym_run_own p env own (fuel - 1) t`
      by simp[Once sym_run_own_def] >>
    pop_assum SUBST1_TAC >>
    `t.sym_base.as_stack = []`
      by (irule sym_step_own_base_stack >> fs[rn_rel_def] >> metis_tac[]) >>
    qpat_x_assum `(?t'. _) \/ _` strip_assume_tac
    >- (qpat_x_assum `!m. m < fuel ==> _` (qspec_then `fuel - 1` mp_tac) >>
        simp[] >> disch_then drule_all >> strip_tac >>
        qexists_tac `SUC fuel'` >> simp[]) >>
    gvs[] >>
    qpat_x_assum `!t fuel. _ ==> ?j fuel2. _`
      (qspecl_then [`t`, `fuel - 1`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `!j. _ ==> ?t'. _` drule >> strip_tac >>
    qpat_x_assum `sym_run_own p env own (fuel - 1) t = _` (fn th => fs[th]) >>
    qpat_x_assum `!m. m < fuel ==> _` (qspec_then `fuel2` mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac >>
    qexists_tac `SUC fuel'` >> simp[]) >>
  `sym_run_own p env own fuel ss = sym_step_own p env own (EL ss.sym_base.as_pc p) ss`
    by simp[Once sym_run_own_def] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!f. _` (qspec_then `0` assume_tac) >>
  qexists_tac `SUC 0` >> gvs[sym_result_rel_def, sym_obs_def]
QED
