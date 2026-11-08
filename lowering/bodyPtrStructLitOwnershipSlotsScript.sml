Theory bodyPtrStructLitOwnershipSlots
Ancestors bodyPtrStructLitOwnershipSteps

Theorem alloc_frame_reserved:
  alloc_frame st st' /\ not_fresh_at st x /\ ~alloc_owned st x ==>
  not_fresh_at st' x /\ ~alloc_owned st' x
Proof rw[alloc_frame_def] >> metis_tac[]
QED

Theorem alloc_run_reserved:
  alloc_run P f Q /\ P st /\ alloc_writers_unique st /\
  f st = (v,st') /\ not_fresh_at st x /\ ~alloc_owned st x ==>
  not_fresh_at st' x /\ ~alloc_owned st' x
Proof
  strip_tac >> irule alloc_frame_reserved >>
  goal_assum (drule_at Any) >> fs[alloc_run_def] >> metis_tac[]
QED
