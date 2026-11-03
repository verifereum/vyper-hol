(* Composition of legal scheduling and final operand flips. *)
Theory dftFrameCompose
Ancestors
  dftFrameLegalSim dftFrameFlipSim dftFrameLegal dftFrameCertificate
  dftFrameSwap dftFrameFacts dftFrameContext dftFrameNormalize dftFrameObserve
  dftRunRel dftScheduleOrder o1PassLift unitShapeDefs contextCodegenRel
  venomWf venomInst relation list

Theorem dft_frame_sim_compose:
  fn_entry_label g = fn_entry_label f /\
  frame_sim L C D f g /\ frame_sim L D E g h ==> frame_sim L C E f h
Proof
  rw[frame_sim_def] >>
  `fn_entry_state g s0` by fs[fn_entry_state_def] >>
  metis_tac[dft_mem_corr_trans, dft_call_corr_trans]
QED

Theorem dft_legal_RTC_frame_sim:
  !f g. RTC dft_legal_swap_fn f g ==>
    !L C. dft_swap_invariant L f ==> frame_sim L C C f g
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt conj_tac >> rpt strip_tac
  >- (rw[frame_sim_def] >> qexistsl [`inst'`, `s'`] >> simp[] >>
      irule dft_reachable_reflexive_observation >>
      metis_tac[dft_swap_invariant_def]) >>
  irule dft_frame_sim_compose >> qexistsl [`C`, `f'`] >>
  metis_tac[dft_legal_swap_frame_sim, dft_legal_swap_fn_projection,
    dft_swap_fn_name_entry, dft_swap_fn_invariant]
QED

Theorem dft_fn_same_context_frame_sim:
  dft_fn_rel f g /\ fn_shape_ok f /\ dft_labels_bound f L ==>
    frame_sim L C C f g
Proof
  strip_tac >>
  `dft_swap_invariant L f` by fs[dft_swap_invariant_def, dft_fn_rel_def] >>
  drule_all dft_fn_legal_certificate >> strip_tac >>
  `fn_entry_label g' = fn_entry_label f` by
    metis_tac[dft_legal_swap_RTC_projection, dft_swap_RTC_name_entry] >>
  irule dft_frame_sim_compose >> qexistsl [`C`, `g'`] >>
  metis_tac[dft_legal_RTC_frame_sim, dft_flip_frame_sim]
QED

Theorem dft_fn_context_frame_sim:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  ctx_labels_bound C L /\ dft_fn_rel f g /\ fn_shape_ok f /\
  dft_labels_bound f L ==> frame_sim L C C' f g
Proof
  strip_tac >> drule_all dft_fn_same_context_frame_sim >>
  rw[frame_sim_def] >>
  `frame_reach C g s0 inst' s'` by metis_tac[dft_frame_reach_context] >>
  metis_tac[]
QED
