(* Frame-local simulation from synchronized anchors and cut observations. *)
Theory dftFrameLegalSim
Ancestors
  dftFrameObserve dftFrameSync dftFrameAnchor dftFrameLegal dftFrameSwap
  o1PassLift venomExecSemantics venomInst venomWf contextCodegenRel

Theorem dft_legal_frame_anchor:
  !C g s0 j t. frame_reach C g s0 j t ==>
    !L f. dft_swap_invariant L f /\ dft_legal_swap_fn f g ==>
      dft_block_anchor C f g s0 j t
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule dft_block_anchor_entry >>
      `dft_swap_fn f g` by metis_tac[dft_legal_swap_fn_projection] >>
      `enters_block f s0 t` by metis_tac[dft_swap_fn_entry] >>
      `?i. active_inst f i t` by metis_tac[dft_swap_fn_active_exists] >>
      metis_tac[frame_reach_rules])
  >- (irule dft_block_anchor_next >>
      metis_tac[dft_swap_invariant_def, dft_swap_fn_wf,
                dft_legal_swap_fn_projection]) >>
  `dft_block_anchor C f g s0 j t` by metis_tac[] >>
  `frame_reach C f s0 j t` by metis_tac[dft_legal_swap_terminator_anchor] >>
  `dft_swap_fn f g` by metis_tac[dft_legal_swap_fn_projection] >>
  `enters_block f s' t'` by metis_tac[dft_swap_fn_entry] >>
  `?i. active_inst f i t'` by metis_tac[dft_swap_fn_active_exists] >>
  irule dft_block_anchor_entry >> metis_tac[frame_reach_rules]
QED

Theorem dft_legal_swap_frame_sim:
  dft_swap_invariant L f /\ dft_legal_swap_fn f g ==> frame_sim L C C f g
Proof
  rw[frame_sim_def] >> irule dft_legal_anchor_observation >>
  metis_tac[dft_legal_frame_anchor]
QED
