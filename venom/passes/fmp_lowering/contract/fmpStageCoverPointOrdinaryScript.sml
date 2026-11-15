(* Progress over kept instructions, including revert-forward tails. *)
Theory fmpStageCoverPointOrdinary
Ancestors
  fmpCoverInvokeIndex
  fmpStageCoverInv fmpStageCoverBack fmpStageCoverMem
  fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  o1PassContract ptrDiscipline contextCodegenRel lowerDloadPtrRawReachable
  venomStepProps venomInstProps venomExecSemantics venomExecProps venomWf
  venomState venomInst passSimulationDefs finite_map words list

Theorem fmp_cov_tidx_mono[local]:
  !j i. i <= j ==>
    fmp_stage_tidx plan root lbl insts i <= fmp_stage_tidx plan root lbl insts j
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `i = SUC j` >- simp[] >>
  `i <= j` by decide_tac >>
  `fmp_stage_tidx plan root lbl insts j <
   fmp_stage_tidx plan root lbl insts (SUC j)` by
    metis_tac[fmp_cov_tidx_lt] >>
  first_x_assum drule >> decide_tac
QED

Theorem fmp_cov_point_ordinary:
  (!restored stk PG G tn fn inst s sm lo u ts fn' stk' ti'.
    frame_reachable vs C stk PG G tn fn inst s /\
    active_inst fn inst s /\ ~s.vs_halted /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
      stk PG G tn fn s lo u ts /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_cov_stack C' stk ts stk' /\ active_inst fn' ti' u ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn' u) /\
  (!fuel s1. step_inst fuel C inst s = OK s1 ==>
    ?inst2.
      frame_reachable vs C stk PG (step_prov PG G inst s1)
        (step_taint inst s s1 tn) fn inst2
        (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
      active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
      ~(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_halted) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  active_inst fn' ti t /\ ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> RETPC_PARAM /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ~((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)) /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    metis_tac[active_inst_block_lookup, get_instruction_def, optionTheory.SOME_11] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
      drule_all fmp_stage_invoke_inst >> strip_tac >>
      gvs[get_instruction_def]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  `ti = inst` by gvs[get_instruction_def] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> qpat_x_assum `step_inst fuel C' inst t = OK t2` mp_tac >>
     simp[step_inst_def, step_inst_base_def]) >>
  Cases_on `in_revert_forward fn s`
  >- suspend "forward" >>
  suspend "ordinary"
QED

Resume fmp_cov_point_ordinary[forward]:
  `?j. revert_forward_pair bb s.vs_inst_idx j` by
    (qpat_x_assum `in_revert_forward fn s` mp_tac >>
     simp[in_revert_forward_def, revert_forward_at_def] >> strip_tac >>
     gvs[] >- metis_tac[] >>
     qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
     simp[revert_forward_pair_def] >> rpt strip_tac >>
     gvs[get_instruction_def, is_terminator_def]) >>
  drule_all fmp_stage_forward_lift >> strip_tac >>
  `t2.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `SUC s.vs_inst_idx <= j` by
    metis_tac[revert_forward_pair_def, arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
      arithmeticTheory.LESS_EQ] >>
  drule fmp_cov_tidx_mono >> strip_tac >>
  simp[fmp_cov_def] >> disj2_tac >>
  qexistsl_tac [`t.vs_inst_idx`,
    `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
       s.vs_current_bb bb.bb_instructions j`] >>
  simp[] >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      s.vs_current_bb bb.bb_instructions s.vs_inst_idx <
   fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
      s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx)` by
    metis_tac[fmp_cov_tidx_lt] >>
  first_x_assum (qspecl_then
    [`fmp_stage_root infos ctx fn`, `fmp_stage_plan infos ctx fn`,
     `s.vs_current_bb`, `bb.bb_instructions`] mp_tac) >> decide_tac
QED

Resume fmp_cov_point_ordinary[ordinary]:
  `terminates (step_inst fuel C' inst t)` by simp[terminates_def] >>
  `~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by simp[] >>
  `terminates (step_inst fuel C inst s)` by
    (irule fmp_stage_back_kept >> metis_tac[]) >>
  `step_inst fuel C inst s = step_inst fuel C inst s` by simp[] >>
  `w2n vs'.vs_initial_fmp = w2n vs'.vs_initial_fmp /\
   w2n fmp = w2n fmp` by simp[] >>
  drule_all fmp_stage_op_step >> strip_tac >>
  `inst' = inst` by
    (drule_all active_inst_block_lookup >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  `r' = OK t2` by metis_tac[step_inst_non_invoke] >>
  Cases_on `step_inst fuel C inst s` >>
  gvs[terminates_def, dead_result_rel_def] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspec_then `F` irule) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ (_ with vs_inst_idx := _) _ _ _`
    (irule_at Any) >> simp[] >> metis_tac[]
QED

Finalise fmp_cov_point_ordinary
