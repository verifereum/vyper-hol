Theory entryStatementTargetSupport
Ancestors
  supportedStmts supportedTargets targetPlaceSimCases

Theorem supported_target_info_index:
  !bt pt e. supported_target_info tops bindings bt = SOME pt /\
    MEM e (target_indices bt) ==> supported_expr tops e
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[supported_target_info_def, target_indices_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem supported_target_index:
  supported_target tops bindings bt /\ MEM e (target_indices bt) ==>
  supported_expr tops e
Proof
  Cases_on `bt` >> simp[supported_target_def, target_indices_def] >>
  rpt BasicProvers.TOP_CASE_TAC >>
  simp[target_indices_def] >> metis_tac[]
QED

Theorem supported_assignment_tuple_index:
  supported_assignment tops bindings target rhs /\
  MEM (BaseTarget bt) targets /\ target = TupleTarget targets /\
  MEM e (target_indices bt) ==> supported_expr tops e
Proof
  simp[supported_assignment_def] >> rpt strip_tac >> gvs[] >>
  gvs[listTheory.EVERY_MEM] >>
  first_x_assum (qspec_then `BaseTarget bt` mp_tac) >>
  simp[] >> metis_tac[supported_target_index]
QED

Theorem supported_assignment_base_index:
  supported_assignment tops bindings (BaseTarget bt) rhs /\
  MEM e (target_indices bt) ==> supported_expr tops e
Proof
  simp[supported_assignment_def] >> rpt strip_tac
  >- metis_tac[supported_target_index] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  Cases_on `x` >> gvs[] >> metis_tac[supported_target_info_index]
QED

Theorem supported_aug_target_index:
  supported_aug_target tops bindings bt /\ MEM e (target_indices bt) ==>
  supported_expr tops e
Proof
  simp[supported_aug_target_def] >> rpt strip_tac >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  Cases_on `x` >> gvs[] >> metis_tac[supported_target_info_index]
QED
