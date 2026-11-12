Theory fmpStageFmpStepsRestoreBounds
Ancestors
  fmpStageFmpStepsRestoreControl fmpStepLayout fmpLowerIndexedProps
  fmpLowerDefs fmpStageRel finite_map list rich_list

Theorem fmp_restore_inst_nonempty:
  fmp_lower_inst infos ctx runner sp inst = SOME (code,sp') ==>
  code <> []
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_restore_indexed_nonempty:
  fmp_lower_indexed infos ctx runner lbl idx sp restores (inst::insts) =
    SOME (code,leftover,sp') ==> code <> []
Proof
  simp[fmp_lower_indexed_cons, AllCaseEqs()] >> rpt strip_tac >>
  drule fmp_restore_inst_nonempty >> gvs[]
QED
