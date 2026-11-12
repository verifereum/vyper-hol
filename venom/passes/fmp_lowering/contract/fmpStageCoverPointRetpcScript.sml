(* RETPC expansion progress; packaging interfaces are hypotheses. *)
Theory fmpStageCoverPointRetpc
Ancestors
  fmpStageCoverInv fmpStageCoverBack fmpStageCoverMem
  fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  ptrDiscipline contextCodegenRel venomStepProps venomExecSemantics
  venomExecProps venomInstProps venomState venomInst finite_map words list

Theorem fmp_cov_point_retpc:
  (!rpolicy D C C' vs vs' fmp eom stk PG G tn fn inst s fuel s1.
    fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel C inst s = OK s1 ==>
    ?inst2. frame_reachable vs C stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_halted) /\
  (!D C C' vs vs' (fmp:256 word) eom stk' fn' ti t fuel t2 n u fn stk PG G tn inst s sm lo ts restored bb'.
    (!fn' C' name ti t fuel t2 n u.
      ALL_DISTINCT (fn_labels fn') /\
      lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
      ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
      step_inst fuel C' ti t = OK t2 /\ 0 < n /\
      (!k. fmp_target_run k C' name t n u) ==>
      !k. fmp_target_run k C' name
        (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' fn.fn_name t n u) /\
    t.vs_current_bb = u.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx + n /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
      stk PG G tn fn s lo u ts /\ fmp_cov_stack C' stk ts stk' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!i. SUC t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
      i < LENGTH bb'.bb_instructions /\
      fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn'
      (t2 with vs_inst_idx := SUC t.vs_inst_idx)) /\
  (!fn' C' name ti t fuel t2 n u.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' name t n u) ==>
    !k. fmp_target_run k C' name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = RETPC_PARAM /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  `terminates (step_inst 0 C inst s)` by
    (irule fmp_stage_back_fmp_ops >> simp[] >> metis_tac[]) >>
  `?s1 n u. step_inst 0 C inst s = OK s1 /\ 1 <= n /\ n <= 2 /\
    (!k. fmp_target_run k C' fn.fn_name t n u) /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk PG (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo u ts` by
    metis_tac[fmp_stage_retpc_step] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  qpat_assum `!rpolicy D C C' vs vs' fmp eom stk PG G tn fn inst s fuel s1. _`
    (drule_all_then strip_assume_tac) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `t.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = s.vs_current_bb` by
    (imp_res_tac fmp_cov_frame_pos >> gvs[]) >>
  `u.vs_inst_idx = t.vs_inst_idx + n` by
    (qpat_assum `!k. fmp_target_run k _ _ _ _ _`
       (qspec_then `0` (strip_assume_tac o REWRITE_RULE [fmp_target_run_def])) >>
     gvs[]) >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  fs[] >>
  qpat_x_assum `!bb. lookup_block s1.vs_current_bb _ = _ ==> _`
    (qspec_then `bb` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup] >>
  `!i. SUC t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
    i < LENGTH bt.bb_instructions /\
    fmp_inserted_op (EL i bt.bb_instructions).inst_opcode` by
    (gen_tac >> strip_tac >>
     `i + 1 = u.vs_inst_idx` by decide_tac >>
     `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        s.vs_current_bb bb.bb_instructions s.vs_inst_idx <
      fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx)` by
       simp[fmp_cov_tidx_lt] >>
     `(if s.vs_inst_idx = 0 then 0 else
         fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
           s.vs_current_bb bb.bb_instructions s.vs_inst_idx) <= i /\
       i < fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
           s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx)` by
       (Cases_on `s.vs_inst_idx = 0` >> gvs[] >> decide_tac) >>
     `i = fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
           s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
           (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
            then 1 else 0) ==>
       MEM (EL s.vs_inst_idx bb.bb_instructions).inst_opcode [DALLOCA; RETPC_PARAM]`
       by simp[] >>
     drule_all fmp_stage_inserted_at >> strip_tac >> gvs[]) >>
  `0 < n` by decide_tac >>
  `t.vs_current_bb = u.vs_current_bb` by metis_tac[] >>
  qpat_assum `!D C C' vs vs' fmp eom stk' fn' ti t fuel t2 n u fn stk PG G tn inst s sm lo ts restored bb'. _`
    (drule_then mp_tac) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ s _ t _` kall_tac >>
  disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
