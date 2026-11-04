Theory dftInvokeOrdinaryBoundary
Ancestors
  dftMixedCrossing dftPendingSuspension dftMixedResidualProbe
  dftOccurrenceMachine dftOccurrenceReplay dftOccurrenceResidual dftOpenErase dftOpenMachine
  venomExecSemantics list arithmetic

(* Separate setup premises are essential: the selected bodies may differ. *)
Theorem dft_pending_two_context_push:
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
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftEnter calleeL 0 csL)
        (DftCaller fnL 0 bbL call sL :: MAP (dft_fill_frame 0) stackL) nL;
      dft_occ_path := path ++ [(visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (path,visit)::l.dft_occ_saved|> /\
  dft_occ_oracle_next w C' r = r with
    <|dft_occ_core := DftOpen (DftEnter calleeR 0 csR)
        (DftCaller fnR 0 bbR call sR :: MAP (dft_fill_frame 0) stackR) nR;
      dft_occ_path := path ++ [(visit,call.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (path,visit)::r.dft_occ_saved|>
Proof
  strip_tac >>
  `eval_operands ops sL = eval_operands ops sR` by
    (irule dft_cut_pair_eval_operands >> qexistsl_tac [`us`, `[]`] >> simp[]) >>
  `eval_operands ops sR = SOME args` by metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `r.dft_occ_core = _` kall_tac >>
      drule_all dft_occ_push >>
      disch_then (qspec_then `\n. w (dft_occ_address l)` mp_tac) >>
      simp[dft_occ_oracle_next_def, dft_erase_def, dft_fill_def,
           dft_fill_control_def, dft_fill_frame_def, MAP_MAP_o, combinTheory.o_DEF,
           MAP_EQ_f] >>
      rpt strip_tac >> Cases_on `x` >> simp[dft_fill_frame_def]) >>
  qpat_x_assum `l.dft_occ_core = _` kall_tac >>
  drule_all dft_occ_push >>
  disch_then (qspec_then `\n. w (dft_occ_address r)` mp_tac) >>
  simp[dft_occ_oracle_next_def, dft_erase_def, dft_fill_def,
           dft_fill_control_def, dft_fill_frame_def, MAP_MAP_o, combinTheory.o_DEF,
           MAP_EQ_f] >>
      rpt strip_tac >> Cases_on `x` >> simp[dft_fill_frame_def]
QED

(* Projections retain the two clocks separately; equality is conditional. *)
Theorem dft_pending_two_context_push_fields:
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
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit ==>
  (dft_occ_oracle_next w C l).dft_occ_core =
    DftOpen (DftEnter calleeL 0 csL)
      (DftCaller fnL 0 bbL call sL :: MAP (dft_fill_frame 0) stackL) nL /\
  (dft_occ_oracle_next w C' r).dft_occ_core =
    DftOpen (DftEnter calleeR 0 csR)
      (DftCaller fnR 0 bbR call sR :: MAP (dft_fill_frame 0) stackR) nR /\
  dft_occ_count (dft_occ_oracle_next w C l) = nL /\
  dft_occ_count (dft_occ_oracle_next w C' r) = nR /\
  (dft_occ_oracle_next w C l).dft_occ_path = path ++ [(visit,call.inst_id)] /\
  (dft_occ_oracle_next w C' r).dft_occ_path = path ++ [(visit,call.inst_id)] /\
  (dft_occ_oracle_next w C l).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w C' r).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w C l).dft_occ_saved = (path,visit)::l.dft_occ_saved /\
  (dft_occ_oracle_next w C' r).dft_occ_saved = (path,visit)::r.dft_occ_saved /\
  (nL = nR ==>
    dft_occ_count (dft_occ_oracle_next w C l) =
    dft_occ_count (dft_occ_oracle_next w C' r))
Proof
  strip_tac >> drule_all dft_pending_two_context_push >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  simp[dft_occ_count_def]
QED
