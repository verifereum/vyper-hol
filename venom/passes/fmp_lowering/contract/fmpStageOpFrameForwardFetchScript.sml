Theory fmpStageOpFrameForwardFetch
Ancestors
  fmpStageControl fmpStageOpBase fmpStageRel fmpStepReclaim
  lowerDloadPtrForward o1PassContract contextCodegenRel venomExecSemantics
  venomExecProofs venomInst venomWf list

Theorem fmp_forward_interval[local]:
  revert_forward_pair bb p j /\ p <= k /\ k <= j ==>
  k < LENGTH bb.bb_instructions /\
  MEM (EL k bb.bb_instructions).inst_opcode [RETURNDATACOPY; ASSIGN; REVERT]
Proof
  strip_tac >>
  `j < LENGTH bb.bb_instructions` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `k < LENGTH bb.bb_instructions` by decide_tac >> simp[] >>
  `get_instruction bb k = SOME (EL k bb.bb_instructions)` by
    simp[get_instruction_def] >>
  drule_all revert_forward_pair_interval_opcode >> simp[] >> metis_tac[]
QED

Theorem fmp_forward_point[local]:
  revert_forward_pair bb p j /\ p <= k /\ k <= j /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ~((lbl,k) IN FDOM (fmp_stage_plan infos ctx fn))
Proof
  strip_tac >> drule_all fmp_forward_interval >> strip_tac >>
  spose_not_then assume_tac >> drule_all fmp_stage_plan_point >>
  strip_tac >> drule fmp_reclaim_point_opcodes >> gvs[]
QED

Theorem fmp_forward_tidx[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
    fn_is_context_entry ctx fn ==> entry_fn_no_params fn) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  revert_forward_pair bb p j ==>
  !h. h <= j-p ==>
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions (p+h) =
    fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions p + h
Proof
  strip_tac >> Induct >> simp[] >> strip_tac >>
  `p < j` by metis_tac[revert_forward_pair_def] >>
  `p <= p+h /\ p+h <= j /\ h <= j-p` by decide_tac >>
  drule_all fmp_forward_interval >> strip_tac >>
  `~((lbl,p+h) IN FDOM (fmp_stage_plan infos ctx fn))` by
    metis_tac[fmp_forward_point] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\ lbl = rl ==>
      rp <> SUC (p+h)` by
    (rpt strip_tac >>
     `lookup_block rl fn.fn_blocks = SOME bb` by metis_tac[] >>
     `SUC (p+h) = rp` by simp[] >>
     `fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by metis_tac[] >>
     drule_all fmp_stage_root_crossing >> disch_tac >>
     qpat_x_assum `MEM _ [RETURNDATACOPY; ASSIGN; REVERT]` mp_tac >> simp[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions (SUC (p+h)) =
    SUC (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      lbl bb.bb_instructions (p+h))` by
    (irule fmp_stage_tidx_suc >> gvs[]) >>
  gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem fmp_forward_fetch_point[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  revert_forward_pair bb p j /\ p <= idx /\ idx <= j ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    get_instruction bb'
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        lbl bb.bb_instructions idx) = SOME (EL idx bb.bb_instructions)
Proof
  strip_tac >> drule_all fmp_forward_interval >> strip_tac >>
  `~((lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn))` by
    metis_tac[fmp_forward_point] >>
  `pre_fmp_opcode (EL idx bb.bb_instructions).inst_opcode /\
   ~MEM (EL idx bb.bb_instructions).inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
    gvs[pre_fmp_opcode_def] >>
  `EL idx bb.bb_instructions = EL idx bb.bb_instructions` by simp[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  qexists_tac `bb'` >> gvs[get_instruction_def]
QED

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
  `p <= p` by simp[] >> drule_all fmp_forward_fetch_point >> strip_tac >>
  qexists_tac `bb'` >> simp[] >> rpt strip_tac >>
  `p <= p+h /\ p+h <= j` by decide_tac >>
  `?b. lookup_block lbl fn'.fn_blocks = SOME b /\
    get_instruction b
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        lbl bb.bb_instructions (p+h)) = SOME (EL (p+h) bb.bb_instructions)` by
    (irule fmp_forward_fetch_point >> metis_tac[]) >>
  `b = bb'` by metis_tac[optionTheory.SOME_11] >>
  drule_all fmp_forward_tidx >> disch_tac >>
  `p+h < LENGTH bb.bb_instructions` by metis_tac[fmp_forward_interval] >>
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
