Theory dftRecursiveCertifiedPush
Ancestors
  dftRecursiveCallProvenance dftRecursiveCallBoundary dftRecursiveCallResidual
  dftInvokeOrdinaryBoundary dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecSemantics list

Theorem dft_certified_frames_canonical[local]:
  !cs ls rs. dft_provenanced_frames fm bm cs ls rs ==>
    MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  Induct >> simp[dft_provenanced_frames_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule dft_provenanced_frame_projection >>
  Cases_on `l` >> Cases_on `r` >>
  simp[dft_recursive_frame_def, dft_fill_frame_def] >> strip_tac >> gvs[]
QED

Theorem dft_provenanced_pending_push:
  dft_cut_pair us [] sL sR /\
  EVERY (\p. ~MEM (Var (FST p)) ops) us /\
  eval_operands ops sL = SOME args /\
  setup_callee calleeL args sL = SOME csL /\
  setup_callee calleeR args sR = SOME csR /\
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL sL) stackL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR sR) stackR nR /\
  get_instruction bbL sL.vs_inst_idx = SOME call /\
  get_instruction bbR sR.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME calleeL /\
  lookup_function nm C'.ctx_functions = SOME calleeR /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  l.dft_occ_saved = saved /\ r.dft_occ_saved = saved /\
  LENGTH saved = LENGTH certs /\
  dft_provenanced_frames fm bm certs stackL stackR /\
  dft_provenanced_frame fm bm (SOME cert)
    (DftCaller fnL 0 bbL call sL) (DftCaller fnR 0 bbR call sR) /\
  dft_certificate_annotation (SOME cert) = DftPending us [] ==>
  ?sl sr.
    (dft_occ_oracle_next w C l).dft_occ_core =
      DftOpen (DftEnter calleeL 0 csL) sl nL /\
    (dft_occ_oracle_next w C' r).dft_occ_core =
      DftOpen (DftEnter calleeR 0 csR) sr nR /\
    dft_provenanced_frames fm bm (SOME cert::certs) sl sr /\
    (dft_occ_oracle_next w C l).dft_occ_saved = (path,visit)::saved /\
    (dft_occ_oracle_next w C' r).dft_occ_saved = (path,visit)::saved /\
    LENGTH ((path,visit)::saved) = LENGTH (SOME cert::certs) /\
    (dft_occ_oracle_next w C l).dft_occ_path = path ++ [(visit,call.inst_id)] /\
    (dft_occ_oracle_next w C' r).dft_occ_path = path ++ [(visit,call.inst_id)] /\
    (dft_occ_oracle_next w C l).dft_occ_visit = 0 /\
    (dft_occ_oracle_next w C' r).dft_occ_visit = 0 /\
    dft_occ_count (dft_occ_oracle_next w C l) = nL /\
    dft_occ_count (dft_occ_oracle_next w C' r) = nR
Proof
  strip_tac >> drule_all dft_pending_two_context_push_fields >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  drule dft_certified_frames_canonical >> strip_tac >>
  qexistsl_tac [`DftCaller fnL 0 bbL call sL::stackL`,
                `DftCaller fnR 0 bbR call sR::stackR`] >> simp[]
QED
