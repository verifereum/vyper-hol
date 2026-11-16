Theory fmpStageOpFrameForwardFetch
Ancestors
  fmpStageCoverForwardInterval
  fmpStageControl fmpStageOpBase fmpStageRel fmpStepReclaim
  lowerDloadPtrForward o1PassContract contextCodegenRel venomExecSemantics
  venomExecProofs venomInst venomWf list

Theorem fmp_forward_fetch_static[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb p j ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    !h. h <= j-p ==> get_instruction bb (p+h) =
      get_instruction bb'
        (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
          lbl bb.bb_instructions p + h)
Proof
  strip_tac >> `p <= j` by metis_tac[revert_forward_pair_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `p <= p` by simp[] >> drule_all fmp_cover_interval_fetch >> strip_tac >>
  qexists_tac `bb'` >> simp[] >> rpt strip_tac >>
  `p <= p+h /\ p+h <= j` by decide_tac >>
  `?b. lookup_block lbl fn'.fn_blocks = SOME b /\
    get_instruction b
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        lbl bb.bb_instructions (p+h)) = SOME (EL (p+h) bb.bb_instructions)` by
    (irule fmp_cover_interval_fetch >> metis_tac[]) >>
  `b = bb'` by metis_tac[optionTheory.SOME_11] >>
  drule_all fmp_cover_interval_tidx >> disch_tac >>
  `p+h < LENGTH bb.bb_instructions` by metis_tac[fmp_cover_interval_opcode] >>
  gvs[get_instruction_def, arithmeticTheory.ADD_COMM]
QED

Theorem fmp_forward_fetch:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = RETURNDATACOPY /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_pair bb s.vs_inst_idx j ==>
  ?fn' bb'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!h. h <= j-s.vs_inst_idx ==>
      get_instruction bb (s.vs_inst_idx+h) =
      get_instruction bb' (t.vs_inst_idx+h))
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once fmp_stage_rel_def] >> strip_tac >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> strip_tac >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by
    (rpt gen_tac >> strip_tac >>
     drule_all fmp_stage_witness_pin >> strip_tac >>
     gvs[o1_fn_shape_def]) >>
  drule_all fmp_forward_fetch_static >> strip_tac >>
  qexists_tac `bb'` >> gvs[arithmeticTheory.ADD_COMM]
QED
