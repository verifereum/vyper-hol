Theory concretizePtrHistoryObservation
Ancestors frameExecutionHistory ptrDiscipline list rich_list

Definition ptr_history_realized_def:
  ptr_history_realized vs0 ctx fn PG h <=>
    !j t. MEM (j,t) h ==>
      ?stk0 G0 tn0. frame_reachable vs0 ctx stk0 PG G0 tn0 fn j t
End

Theorem ptr_history_realized_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    frame_reachable vs0 ctx stk PG G tn fn inst s /\
    ptr_history_realized vs0 ctx fn PG h /\
    LIST_REL (\f h0. ptr_history_realized vs0 ctx f.cf_fn f.cf_params h0) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[ptr_history_realized_def] >>
      metis_tac[cj 1 frame_reachable_rules])
  >- (rpt strip_tac >> gvs[ptr_history_realized_def, MEM_APPEND] >>
      metis_tac[cj 2 frame_reachable_rules])
  >- (rpt strip_tac >> gvs[ptr_history_realized_def, MEM_APPEND] >>
      metis_tac[cj 3 frame_reachable_rules])
  >- (rpt strip_tac >> gvs[ptr_history_realized_def] >>
      metis_tac[cj 4 frame_reachable_rules]) >>
  rpt strip_tac >> gvs[ptr_history_realized_def, MEM_APPEND] >>
  metis_tac[cj 5 frame_reachable_rules]
QED

Theorem ptr_history_current_observation:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ MEM (j,t) h ==>
  ?stk0 G0 tn0. frame_reachable vs0 ctx stk0 PG G0 tn0 fn j t
Proof
  metis_tac[ptr_history_realized_invariant, ptr_history_realized_def]
QED

Theorem ptr_history_saved_observation:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  n < LENGTH stk /\ MEM (j,t) (EL n hs) ==>
  ?stk0 G0 tn0. frame_reachable vs0 ctx stk0 (EL n stk).cf_params G0 tn0
    (EL n stk).cf_fn j t
Proof
  strip_tac >> drule ptr_history_realized_invariant >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  metis_tac[ptr_history_realized_def]
QED
