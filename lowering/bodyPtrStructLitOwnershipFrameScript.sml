Theory bodyPtrStructLitOwnershipFrame
Ancestors bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
          loweringShapeRules

Theorem alloc_run_shape_frame:
  shape_step internal LP P f Q /\ shape_stable R /\
  alloc_run (\st. shape_state st /\ P st) f A ==>
  alloc_run (\st. shape_state st /\ R st /\ P st) f
    (\v st. shape_state st /\ R st /\ Q v st /\ A v st)
Proof
  strip_tac >>
  drule_all shape_step_frame >> strip_tac >>
  drule_all alloc_run_shape_join >>
  strip_tac >> irule alloc_run_conseq >>
  goal_assum (drule_at Any) >> simp[]
QED
