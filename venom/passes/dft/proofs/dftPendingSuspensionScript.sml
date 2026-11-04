(* Pending output-list specialization of structural hidden-caller transport. *)
Theory dftPendingSuspension
Ancestors
  dftInaccessibleCaller dftMixedResidualProbe dftOccurrenceSuspended
  dftOccurrenceReturn dftOccurrenceResidual dftOpenErase dftOpenMachine
  dftOccurrenceMachine venomExecSemantics venomState arithmetic list

Theorem dft_pending_suspended_hidden:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r <=>
  dft_hidden_caller (dft_pending_frames us) fL fR tL tR sL sR path visit l r
Proof
  simp[dft_pending_suspended_def, dft_hidden_caller_def]
QED

Theorem dft_pending_return_cut:
  dft_cut_pair us [] sL sR /\
  EVERY (\p. ~MEM (FST p) outs) us /\
  dft_restore outs ret cs sL = SOME afterL /\
  dft_restore outs ret cs sR = SOME afterR ==>
  dft_cut_pair us [] afterL afterR
Proof
  strip_tac >> irule dft_restore_cut_pair >> simp[] >> metis_tac[]
QED

Definition dft_pending_resumed_def:
  dft_pending_resumed us frameL frameR tailL tailR savedL savedR path visit l r <=>
    ?fnL fnR bbL bbR call sL sR afterL afterR ret cs nL nR.
      frameL = DftCaller fnL 0 bbL call sL /\
      frameR = DftCaller fnR 0 bbR call sR /\
      dft_restore call.inst_outputs ret cs sL = SOME afterL /\
      dft_restore call.inst_outputs ret cs sR = SOME afterR /\
      dft_cut_pair us [] afterL afterR /\
      l.dft_occ_core = DftOpen (DftAt fnL 0 bbL
        (afterL with vs_inst_idx := SUC sL.vs_inst_idx)) tailL nL /\
      r.dft_occ_core = DftOpen (DftAt fnR 0 bbR
        (afterR with vs_inst_idx := SUC sR.vs_inst_idx)) tailR nR /\
      l.dft_occ_saved = savedL /\ r.dft_occ_saved = savedR /\
      l.dft_occ_path = path /\ r.dft_occ_path = path /\
      l.dft_occ_visit = visit /\ r.dft_occ_visit = visit
End

Definition dft_pending_exit_def:
  dft_pending_exit us fL fR tL tR sL sR path visit l r <=>
    dft_pending_resumed us fL fR tL tR sL sR path visit l r \/
    dft_suspend_cleared l r
End

Theorem dft_pending_distinguished_return:
  dft_pending_frames us (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnL 0 bbL call sL::tailL) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fnR 0 bbR call sR::tailR) nR /\
  l.dft_occ_saved = (path,visit)::savedL /\
  r.dft_occ_saved = (path,visit)::savedR /\
  MAP (dft_fill_frame 0) tailL = tailL /\
  MAP (dft_fill_frame 0) tailR = tailR ==>
  dft_pending_exit us (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) tailL tailR savedL savedR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >> rewrite_tac[dft_pending_exit_def] >>
  Cases_on `dft_restore call.inst_outputs ret cs sL`
  >- (`dft_restore call.inst_outputs ret cs sR = NONE` by
        metis_tac[dft_restore_pair_failure] >>
      disj2_tac >> simp[dft_suspend_cleared_def] >>
      metis_tac[dft_suspend_pop_failure]) >>
  `?afterR. dft_restore call.inst_outputs ret cs sR = SOME afterR` by
    (Cases_on `dft_restore call.inst_outputs ret cs sR` >>
     metis_tac[dft_restore_pair_failure]) >>
  `call.inst_opcode = INVOKE /\ dft_cut_pair us [] x afterR` by
    (fs[dft_pending_frames_def] >> metis_tac[dft_pending_return_cut]) >>
  disj1_tac >>
  drule_all dft_suspend_pop >> disch_tac >>
  rev_drule_all dft_suspend_pop >> disch_tac >>
  simp[dft_pending_resumed_def] >>
  metis_tac[dft_suspend_pop]
QED

Theorem dft_pending_boundary_step:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r /\
  dft_hidden_return fL fR tL tR sL sR path visit l r ==>
  dft_pending_exit us fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_hidden_return_def, dft_pending_suspended_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  Cases_on `fL` >> Cases_on `fR` >> gvs[dft_pending_frames_def] >>
  irule dft_pending_distinguished_return >>
  simp[dft_pending_frames_def] >> metis_tac[]
QED

Theorem dft_pending_suspended_next:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
  dft_pending_suspended us fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_pending_exit us fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `dft_hidden_caller (dft_pending_frames us) fL fR tL tR sL sR path visit l r` by
    simp[GSYM dft_pending_suspended_hidden] >>
  drule dft_hidden_caller_next >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  metis_tac[dft_pending_boundary_step, dft_pending_suspended_hidden,
            dft_pending_exit_def]
QED

Theorem dft_pending_suspended_prefix:
  !j l r. dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
    ((!k. k <= j ==>
       dft_pending_suspended us fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) k l)
         (FUNPOW (dft_occ_oracle_next w C) k r)) \/
     ?h. 0 < h /\ h <= j /\
       dft_pending_exit us fL fR tL tR sL sR path visit
         (FUNPOW (dft_occ_oracle_next w C) h l)
         (FUNPOW (dft_occ_oracle_next w C) h r) /\
       !k. k < h ==>
         dft_pending_suspended us fL fR tL tR sL sR path visit
           (FUNPOW (dft_occ_oracle_next w C) k l)
           (FUNPOW (dft_occ_oracle_next w C) k r))
Proof
  Induct_on `j`
  >- simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (first_assum (qspec_then `j` mp_tac) >> rewrite_tac[LESS_EQ_REFL] >>
      disch_tac >> drule dft_pending_suspended_next >>
      disch_then (qspecl_then [`w`, `C`] strip_assume_tac)
      >- (disj1_tac >> rpt strip_tac >>
          Cases_on `k = SUC j` >> gvs[FUNPOW_SUC] >>
          first_x_assum irule >> decide_tac) >>
      disj2_tac >> qexists `SUC j` >> simp[FUNPOW_SUC] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  disj2_tac >> qexists `h` >> simp[] >> decide_tac
QED
