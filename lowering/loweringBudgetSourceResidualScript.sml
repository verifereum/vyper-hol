(* Concrete source-entry residuals, retaining the actual execution state. *)
Theory loweringBudgetSourceResidual
Ancestors vyperState[qualified,ignore_grammar]
  sourceCallCount sourceCallCountEntryReplay vyperEvalOutcomeSuffix
  list option pair
Libs BasicProvers

Theorem lower_budget_call_entry_residual_suffix:
  !os obs am tx res st rest.
    call_entry_run os obs am tx = SOME (res,st) /\
    st.outcomes = SOME rest ==>
    ?used. os = used ++ rest
Proof
  rpt gen_tac >>
  simp_tac bool_ss [call_entry_run_def, LET_THM] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule fn_entry_run_outcomes_suffix >>
  simp[outcome_suffix_def]
QED
