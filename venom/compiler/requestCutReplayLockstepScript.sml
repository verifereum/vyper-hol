Theory requestCutReplayLockstep
Ancestors
  e2eRequestCutDefs o1FrameLockstep o1PassContract o1ContractMakeSsaReplay
  makeSsaCurrentLockstep makeSsaCurrentSim unitTransformDefs o1RequestContract
  frameRawProjection concretizePtrCoverageStaticMemReachability o1PassLift
  venomPassSchedule venomWf ptrDiscipline passSimulationDefs stateFrame venomExecSemantics
  venomState finite_map list o1ContractMakeSsaPtrOk o1ContractMakeSsaPtrRows
  o1ContractMakeSsaPtrPos lowerDloadRequestObservation

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
