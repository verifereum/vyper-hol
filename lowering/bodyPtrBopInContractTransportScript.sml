Theory bodyPtrBopInContractTransport
Ancestors bodyPtrBopInLoopContract venomState finite_map

Theorem membership_loop_frame_sym:
  membership_loop_frame sa G0 tn0 s0 G1 tn1 s1 ==>
  membership_loop_frame sa G1 tn1 s1 G0 tn0 s0
Proof
  simp[membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `s1 = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_load_contract_rebase:
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G0 tn0 s0 /\
  membership_loop_frame sa G0 tn0 s0 G1 tn1 s1 ==>
  membership_load_contract D ctx fn PG sa skip is_ctor imm loc ws G1 tn1 s1
Proof
  strip_tac >> fs[membership_load_contract_def] >> rpt strip_tac >>
  `membership_loop_frame sa G0 tn0 s0 G tn s` by
    metis_tac[membership_loop_frame_trans] >>
  first_x_assum drule_all >> strip_tac >>
  `membership_loop_frame sa G1 tn1 s1 G' tn' t` by
    metis_tac[membership_loop_frame_sym, membership_loop_frame_trans] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
