Theory dftRecursiveCallBoundary
Ancestors
  dftRecursiveCallResidual dftInvokeOrdinaryBoundary dftPendingSuspension
  dftOccurrenceResidual dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecSemantics list

Theorem dft_setup_callee_header:
  (NULL f.fn_blocks <=> NULL g.fn_blocks) /\
  (~NULL f.fn_blocks ==>
    (HD f.fn_blocks).bb_label = (HD g.fn_blocks).bb_label) ==>
  setup_callee f args s = setup_callee g args s
Proof
  strip_tac >> Cases_on `NULL f.fn_blocks` >> gvs[setup_callee_def]
QED

Theorem dft_recursive_setup_callee:
  dft_cut_pair us vs s t /\
  (NULL f.fn_blocks <=> NULL g.fn_blocks) /\
  (~NULL f.fn_blocks ==>
    (HD f.fn_blocks).bb_label = (HD g.fn_blocks).bb_label) ==>
  setup_callee f args s = setup_callee g args t
Proof
  strip_tac >> drule dft_cut_pair_setup_callee >>
  disch_then (qspecl_then [`f`, `args`] assume_tac) >>
  drule_all dft_setup_callee_header >> metis_tac[]
QED

Theorem dft_recursive_frames_canonical[local]:
  !anns ls rs. dft_recursive_frames fm bm anns ls rs ==>
    MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  Induct >> simp[dft_recursive_frames_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `l` >> Cases_on `r` >>
  gvs[dft_recursive_frame_def, dft_fill_frame_def]
QED

Theorem dft_recursive_pending_push:
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
  LENGTH saved = LENGTH anns /\
  dft_recursive_frames fm bm anns stackL stackR /\
  dft_recursive_frame fm bm (DftPending us [])
    (DftCaller fnL 0 bbL call sL) (DftCaller fnR 0 bbR call sR) ==>
  ?sl sr.
    (dft_occ_oracle_next w C l).dft_occ_core =
      DftOpen (DftEnter calleeL 0 csL) sl nL /\
    (dft_occ_oracle_next w C' r).dft_occ_core =
      DftOpen (DftEnter calleeR 0 csR) sr nR /\
    dft_recursive_frames fm bm (DftPending us []::anns) sl sr /\
    (dft_occ_oracle_next w C l).dft_occ_saved = (path,visit)::saved /\
    (dft_occ_oracle_next w C' r).dft_occ_saved = (path,visit)::saved /\
    LENGTH ((path,visit)::saved) = LENGTH (DftPending us []::anns) /\
    (dft_occ_oracle_next w C l).dft_occ_path = path ++ [(visit,call.inst_id)] /\
    (dft_occ_oracle_next w C' r).dft_occ_path = path ++ [(visit,call.inst_id)] /\
    (dft_occ_oracle_next w C l).dft_occ_visit = 0 /\
    (dft_occ_oracle_next w C' r).dft_occ_visit = 0 /\
    dft_occ_count (dft_occ_oracle_next w C l) = nL /\
    dft_occ_count (dft_occ_oracle_next w C' r) = nR
Proof
  strip_tac >> drule_all dft_pending_two_context_push_fields >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  drule dft_recursive_frames_canonical >> strip_tac >>
  qexistsl_tac [`DftCaller fnL 0 bbL call sL::stackL`,
                `DftCaller fnR 0 bbR call sR::stackR`] >> simp[]
QED
