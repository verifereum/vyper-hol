Theory dftRecursiveCallReturn
Ancestors
  dftRecursiveCallResidual dftRecursiveCallBoundary dftPendingSuspension
  dftOccurrenceResidual dftOccurrenceReturn dftOccurrenceSuspended
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomState list

(* Pop only the top payload. Common return data is a premise, not an
   execution-simulation conclusion. The arbitrary paired tail is untouched. *)
Theorem dft_recursive_pending_return:
  dft_recursive_frames fm bm (DftPending us []::anns)
    (DftCaller fnL 0 bbL call sL::tailL)
    (DftCaller fnR 0 bbR call sR::tailR) /\
  dft_restore call.inst_outputs ret cs sL = SOME afterL /\
  dft_restore call.inst_outputs ret cs sR = SOME afterR ==>
  dft_cut_pair us [] afterL afterR /\
  dft_cut_pair us []
    (afterL with vs_inst_idx := SUC sL.vs_inst_idx)
    (afterR with vs_inst_idx := SUC sR.vs_inst_idx) /\
  dft_recursive_frames fm bm anns tailL tailR
Proof
  simp[dft_recursive_frames_cons, dft_recursive_frame_def,
       dft_recursive_payload_def] >> strip_tac >>
  `EVERY (\p. ~MEM (FST p) call.inst_outputs) us` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `dft_cut_pair us [] afterL afterR` by
    (irule dft_pending_return_cut >> metis_tac[]) >>
  simp[] >>
  gvs[dft_cut_pair_def, dft_cut_data_def] >> metis_tac[]
QED

Theorem dft_recursive_plain_return:
  dft_recursive_frames fm bm (DftPlain::anns)
    (DftCaller fnL 0 bbL call sL::tailL)
    (DftCaller fnR 0 bbR call sR::tailR) /\
  dft_restore call.inst_outputs ret cs sL = SOME afterL /\
  dft_restore call.inst_outputs ret cs sR = SOME afterR ==>
  afterL = afterR /\
  (afterL with vs_inst_idx := SUC sL.vs_inst_idx) =
    (afterR with vs_inst_idx := SUC sR.vs_inst_idx) /\
  dft_recursive_frames fm bm anns tailL tailR
Proof
  simp[dft_recursive_frames_cons, dft_recursive_frame_def,
       dft_recursive_payload_def] >> rpt strip_tac >> gvs[]
QED

(* No old annotation or pending value is required after a clearing step. *)
Theorem dft_recursive_cleared:
  l.dft_occ_core = DftOpen ctlL [] nL /\
  r.dft_occ_core = DftOpen ctlR [] nR /\
  l.dft_occ_saved = [] /\ r.dft_occ_saved = [] ==>
  dft_recursive_frames fm bm [] [] [] /\
  LENGTH l.dft_occ_saved = LENGTH ([]:dft_call_annotation list) /\
  LENGTH r.dft_occ_saved = LENGTH ([]:dft_call_annotation list)
Proof
  simp[]
QED
