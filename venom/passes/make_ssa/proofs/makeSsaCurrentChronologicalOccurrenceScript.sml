Theory makeSsaCurrentChronologicalOccurrence
Ancestors makeSsaCurrentChronologicalLedger makeSsaCurrentExecutionHistory
  makeSsaCurrentSemanticHistory venomExecSemantics list rich_list pair

Theorem current_chronological_append:
  !mid suffix finish. current_chronological fn ctx mid suffix finish ==>
  !start prefix. current_chronological fn ctx start prefix mid ==>
    current_chronological fn ctx start (prefix ++ suffix) finish
Proof
  ho_match_mp_tac current_chronological_ind >> rpt strip_tac
  >- simp[] >>
  pure_rewrite_tac[APPEND_ASSOC] >> irule (cj 2 current_chronological_rules) >>
  metis_tac[]
QED

Theorem current_chronological_occurrence:
  !start log finish. current_chronological fn ctx start log finish ==>
  current_chronological fn ctx start log finish /\
  (!k. k < LENGTH log ==>
  ?loc before phases writes next after suffix.
    log = TAKE k log ++ [(phases,writes)] ++ suffix /\
    current_chronological fn ctx start (TAKE k log) (loc,before) /\
    current_execution_edge fn ctx loc before phases (SOME next) (OK after) after /\
    current_semantic_history 0 ctx phases before writes (OK after) after /\
    current_chronological fn ctx (next,after) suffix finish)
Proof
  ho_match_mp_tac current_chronological_ind >> simp[current_chronological_empty] >>
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule (cj 2 current_chronological_rules) >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `k < LENGTH log`
  >- (first_x_assum drule >> strip_tac >>
      qexistsl_tac [`loc'`, `before'`, `phases'`, `writes'`, `next'`, `after'`,
        `suffix ++ [(phases,writes)]`] >>
      `k - LENGTH log = 0` by decide_tac >>
      simp[TAKE_APPEND, APPEND_ASSOC] >>
      irule (cj 2 current_chronological_rules) >> metis_tac[]) >>
  `k = LENGTH log` by decide_tac >> gvs[] >>
  qexistsl_tac [`loc`, `before`, `phases`, `writes`, `next`, `after`, `[]`] >>
  simp[TAKE_APPEND, current_chronological_rules]
QED

Theorem current_chronological_occurrence_prefix:
  !fn ctx start log finish k. current_chronological fn ctx start log finish /\ k < LENGTH log ==>
  ?loc before phases writes next after suffix.
    log = TAKE k log ++ [(phases,writes)] ++ suffix /\
    current_actual_prefix fn ctx (FST start) (SND start)
      (current_ledger_phases (TAKE k log)) (SOME loc) (OK before) before /\
    current_execution_edge fn ctx loc before phases (SOME next) (OK after) after /\
    current_semantic_history 0 ctx phases before writes (OK after) after /\
    current_chronological fn ctx (next,after) suffix finish
Proof
  rpt gen_tac >> strip_tac >> drule current_chronological_occurrence >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`loc`, `before`, `phases`, `writes`, `next`, `after`, `suffix`] >>
  simp[] >>
  qpat_x_assum `current_chronological _ _ _ (TAKE _ _) _`
    (mp_tac o MATCH_MP current_chronological_prefix) >> simp[]
QED
