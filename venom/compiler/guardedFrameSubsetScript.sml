Theory guardedFrameSubset
Ancestors
  guardedFrameReachable ptrDiscipline frameRawProjection

Theorem guarded_frame_subset:
  !vs ctx stk PG G tn fn inst s.
    guarded_frame_reachable vs ctx stk PG G tn fn inst s ==>
    frame_reachable vs ctx stk PG G tn fn inst s
Proof
  ho_match_mp_tac guarded_frame_reachable_ind >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[frame_reachable_rules]
QED

Theorem guarded_raw_subset:
  !vs ctx fn inst s.
    EVERY wf_function ctx.ctx_functions /\
    guarded_raw_reachable vs ctx fn inst s ==>
    raw_reachable vs ctx fn inst s
Proof
  simp[guarded_raw_reachable_def] >>
  metis_tac[guarded_frame_subset, frame_reachable_raw]
QED
