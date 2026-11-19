Theory requestCutReplayLockstep
Ancestors
  e2eRequestCutDefs o1FrameLockstep o1PassContract o1ContractMakeSsaReplay
  makeSsaCurrentLockstep makeSsaCurrentSim unitTransformDefs o1RequestContract
  frameRawProjection concretizePtrCoverageStaticMemReachability o1PassLift
  venomPassSchedule venomWf ptrDiscipline passSimulationDefs stateFrame venomExecSemantics
  venomState finite_map list o1ContractMakeSsaPtrOk o1ContractMakeSsaPtrRows
  o1ContractMakeSsaPtrPos lowerDloadRequestObservation

Theorem lockstep_ctx_rq_upto:
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  EVERY wf_function C.ctx_functions ==>
  ctx_rq_upto D k C C' vs vs
Proof
  simp[ctx_rq_upto_def] >> rpt strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `t'.vs_requests = s.vs_requests` by
    (fs[state_rel_def] >> metis_tac[execution_frame_fields]) >>
  `raw_reachable vs C fn inst s` by
    metis_tac[frameRawProjectionTheory.frame_reachable_raw] >>
  qexistsl_tac [`fn`, `inst`, `s`] >> fs[request_agree_except_refl]
QED

Theorem lockstep_cut_halt[local]:
  frame_reachable vs C' stk' PG G' tn' fn' inst' s' /\ request_cut k s' /\
  inst'.inst_opcode <> INVOKE /\ step_inst fuel C' inst' s' = Halt h' /\
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ?stk G tn fn inst s h.
    frame_reachable vs C stk PG G tn fn inst s /\ request_cut k s /\
    active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel C inst s = Halt h /\ execution_frame h' = execution_frame h /\
    (step_taint inst' s' h' tn').t_stor = (step_taint inst s h tn).t_stor /\
    (step_taint inst' s' h' tn').t_trans = (step_taint inst s h tn).t_trans /\
    (step_taint inst' s' h' tn').t_imm = (step_taint inst s h tn).t_imm /\
    ret_taint tn' inst' s' = ret_taint tn inst s
Proof
  strip_tac >> drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (rpt strip_tac >> metis_tac[step_inst_copy_not_intret]) >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_halt >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  `request_cut k s` by
    (fs[request_cut_def] >> metis_tac[state_rel_def, execution_frame_fields]) >>
  `ghost_rel FEMPTY (step_prov PG G inst h) (step_taint inst s h tn)
     (step_prov PG G' inst' h') (step_taint inst' s' h' tn')` by
    (irule step_ghost_pair >> simp[vars_rel_def, out_rename_ok_def] >>
     reverse conj_tac >- (qexists_tac `sg` >> simp[]) >> fs[]) >>
  `ret_taint tn' inst' s' = ret_taint tn inst s` by metis_tac[ret_taint_pair] >>
  qexistsl_tac [`stk`, `G`, `tn`, `fn`, `inst`, `s`, `h`] >>
  fs[ghost_rel_def]
QED

Theorem lockstep_taint_within_rq_upto:
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within_rq_upto D k C vs ==> taint_within_rq_upto D k C' vs
Proof
  rewrite_tac[taint_within_rq_upto_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all lockstep_req_step >> strip_tac >>
      rename1 `frame_reachable vs C _ _ _ _ _ _ source` >>
      imp_res_tac execution_frame_fields >>
      `request_cut k source` by fs[request_cut_def] >>
      first_x_assum drule_all >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule_all lockstep_cut_halt >> strip_tac >>
  imp_res_tac execution_frame_fields >> first_x_assum drule_all >> metis_tac[]
QED

Theorem make_ssa_stage_lockstep:
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions ==>
  lockstep_ctx (\fn fn' pos.
    pos = make_ssa_pos fn fn' /\ make_ssa_input_ok fn /\ o1_fn_shape C fn /\
    ?sup sup'. ir_supply_covers_fn sup fn /\ ir_supply_inst_ok sup /\
      make_ssa_current_fn sup fn = (fn',sup')) L C C'
Proof
  strip_tac >>
  `C'.ctx_entry = C.ctx_entry /\
   LIST_REL (\f g. ?sup sup'. ir_supply_covers_fn sup f /\ ir_supply_inst_ok sup /\
      make_ssa_current_fn sup f = (g,sup'))
      C.ctx_functions C'.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >> drule make_ssa_pass_step_replay >> simp[]) >>
  `LIST_REL fn_bisim C.ctx_functions C'.ctx_functions` by
    (fs[LIST_REL_EL_EQN, o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
     `make_ssa_input_ok (EL n C.ctx_functions) /\ o1_fn_shape C (EL n C.ctx_functions)` by
       metis_tac[] >>
     irule make_ssa_current_fn_fn_bisim >>
     fs[o1_fn_shape_def, make_ssa_input_ok_def] >> metis_tac[]) >>
  `ctx_bisim C C'` by metis_tac[fn_bisim_ctx_bisim] >>
  simp[lockstep_ctx_def, LIST_REL_EL_EQN] >>
  fs[LIST_REL_EL_EQN, o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
  `make_ssa_input_ok (EL n C.ctx_functions) /\ o1_fn_shape C (EL n C.ctx_functions)` by metis_tac[] >>
  `fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by metis_tac[] >>
  fs[fn_bisim_def] >>
  irule make_ssa_current_fn_frame_lockstep >> fs[o1_fn_shape_def] >> metis_tac[]
QED

Theorem make_ssa_stage_ptr_discipline_rq_upto:
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ ptr_discipline_rq_upto lo k C vs ==>
  ptr_discipline_rq_upto lo k C' vs
Proof
  strip_tac >> drule_all make_ssa_stage_lockstep >>
  disch_then (qspec_then `vs.vs_labels` assume_tac) >>
  `LIST_REL (\f g. make_ssa_input_ok f /\ o1_fn_shape C f /\
      ?su su'. ir_supply_covers_fn su f /\ ir_supply_inst_ok su /\
        make_ssa_current_fn su f = (g,su')) C.ctx_functions C'.ctx_functions` by
    (fs[lockstep_ctx_def, LIST_REL_EL_EQN] >>
     gen_tac >> strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  `(ctx_has_dalloca C' ==> ctx_has_dalloca C)` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM, MEM_EL, LIST_REL_EL_EQN] >>
     strip_tac >> rename1 `n < LENGTH C'.ctx_functions` >>
     qpat_x_assum `!m. m < LENGTH C.ctx_functions ==> _` (qspec_then `n` mp_tac) >>
     simp[] >> strip_tac >> fs[o1_fn_shape_def] >>
     `EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts (EL n C.ctx_functions))` by
       (irule make_ssa_current_fn_dalloca >> simp[] >>
        qexistsl_tac [`EL n C'.ctx_functions`, `su`, `su'`] >>
        simp[EXISTS_MEM, MEM_EL] >> metis_tac[]) >>
     gvs[EXISTS_MEM] >> metis_tac[MEM_EL]) >>
  qpat_x_assum `ptr_discipline_rq_upto lo k C vs` mp_tac >>
  rewrite_tac[ptr_discipline_rq_upto_def] >> strip_tac >>
  simp[ptr_discipline_rq_upto_def] >> conj_tac
  >- (qexists_tac `P` >> fs[EVERY_EL, LIST_REL_EL_EQN] >> rpt strip_tac >>
      `n < LENGTH C.ctx_functions` by simp[] >>
      ntac 2 (first_x_assum drule >> strip_tac) >>
      fs[o1_fn_shape_def] >> drule_all make_ssa_current_fn_ptr_ok >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C' stk' PG G' tn' fn' inst' s'` >>
  drule_all frame_reachable_lockstep >> strip_tac >>
  rename1 `frame_reachable vs C stk PG G tn fn inst s` >>
  fs[] >> drule_all lockstep_rel >> strip_tac >>
  `s'.vs_requests = s.vs_requests /\ s'.vs_allocas = s.vs_allocas /\
   s'.vs_fmp = s.vs_fmp /\ s'.vs_initial_fmp = s.vs_initial_fmp` by
    (fs[state_rel_def] >> drule execution_frame_fields >> simp[]) >>
  `request_cut k s` by fs[request_cut_def] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
   (ctx_has_dalloca C ==> allocas_below_fmp s)` by metis_tac[] >>
  `p /\ in_revert_forward fn s ==> in_revert_forward fn' s'` by
    (Cases_on `p` >> fs[o1_fn_shape_def] >> drule_all make_ssa_lockstep_revert >> simp[]) >>
  `p /\ about_to_revert fn inst s ==> about_to_revert fn' inst' s'` by
    (Cases_on `p` >> fs[o1_fn_shape_def] >> drule_all make_ssa_lockstep_revert >> simp[]) >>
  `~p /\ inst'.inst_opcode = NOP ==> inst'.inst_operands = []` by
    (strip_tac >> gvs[]) >>
  drule_all lockstep_ptr_rows >> simp[] >>
  fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

(* Both SSA passes preserve the recorded snapshot at a matched visit. *)
Theorem lockstep_recording_pair:
  frame_reachable vs C' stk' PG G' tn' fn' i' t /\
  i'.inst_opcode <> INVOKE /\ step_inst fuel C' i' t = OK t' /\
  LENGTH t.vs_requests < LENGTH t'.vs_requests /\
  lockstep_ctx Q vs.vs_labels C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
  ?stk G tn fn i s s'.
    frame_reachable vs C stk PG G tn fn i s /\ active_inst fn i s /\
    i.inst_opcode = i'.inst_opcode /\ step_inst fuel C i s = OK s' /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    s'.vs_requests = t'.vs_requests /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans
Proof
  strip_tac >>
  `i'.inst_opcode <> ASSIGN /\ i'.inst_opcode <> NOP` by
    (drule_all ld_request_growth_external >> rw[MEM] >> fs[]) >>
  drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_step >> disch_then (qx_choose_then `s'` strip_assume_tac) >>
  qexistsl_tac [`stk`,`G`,`tn`,`fn`,`inst`,`s`,`s'`] >>
  fs[state_rel_def, inst_pair_def, ghost_rel_def] >>
  imp_res_tac execution_frame_fields
QED
