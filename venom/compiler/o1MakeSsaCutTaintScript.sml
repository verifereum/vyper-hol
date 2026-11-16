(* Cut-guarded taint transport.  In the halt case the source pre-state
   is retained until its gas cut has been used. *)
Theory o1MakeSsaCutTaint
Ancestors
  o1SafeUpto o1FrameLockstep o1ContractMakeSsa makeSsaCurrentLockstep
  makeSsaCurrentSim o1PassLift o1PassContract ptrDiscipline unitMemInv stateFrame list

Theorem taint_within_upto_lockstep:
  lockstep_ctx Q vs.vs_labels C C' /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within_upto D n C vs ==>
  taint_within_upto D n C' vs
Proof
  rewrite_tac[taint_within_upto_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rename1 `frame_reachable vs C' stk2 PG G2 tn2 fn2 inst2 s2` >>
      drule_all lockstep_req_step >> strip_tac >>
      `gas_cut n vs s` by metis_tac[gas_cut_execution_frame] >>
      first_x_assum drule_all >>
      imp_res_tac execution_frame_fields >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `frame_reachable vs C' stk' PG G' T0' fn' inst' s'` >>
  rename1 `step_inst fuel C' inst' s' = Halt h'` >>
  drule_all frame_reachable_lockstep >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `gas_cut n vs s` by
    (irule gas_cut_execution_frame >> goal_assum (drule_at Any) >>
     fs[state_rel_def]) >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (rpt strip_tac >> metis_tac[step_inst_copy_not_intret]) >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_halt >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  `ghost_rel FEMPTY (step_prov PG G inst h) (step_taint inst s h tn)
     (step_prov PG G' inst' h') (step_taint inst' s' h' T0')` by
    (irule step_ghost_pair >> simp[vars_rel_def, out_rename_ok_def] >>
     reverse conj_tac >- (qexists `sg` >> simp[]) >> fs[]) >>
  `ret_taint T0' inst' s' = ret_taint tn inst s` by
    metis_tac[ret_taint_pair] >>
  first_x_assum drule_all >>
  imp_res_tac execution_frame_fields >> fs[ghost_rel_def]
QED

Theorem make_ssa_stage_taint_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within_upto D n C vs ==>
  taint_within_upto D n C' vs
Proof
  strip_tac >>
  drule make_ssa_stage_functions >> strip_tac >>
  drule make_ssa_stage_length >> strip_tac >>
  `ctx_bisim C C'` by (irule make_ssa_stage_bisim >> metis_tac[]) >>
  `lockstep_ctx (\fn fn' pos. T) vs.vs_labels C C'` by
    (simp[lockstep_ctx_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     drule_all make_ssa_stage_el >> strip_tac >>
     `fn_bisim (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` by
       (irule make_ssa_current_fn_fn_bisim >>
        gvs[make_ssa_input_ok_def] >> metis_tac[]) >>
     fs[fn_bisim_def] >>
     qexists `make_ssa_pos (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` >>
     irule make_ssa_current_fn_frame_lockstep >> metis_tac[]) >>
  drule_all taint_within_upto_lockstep >> simp[]
QED
