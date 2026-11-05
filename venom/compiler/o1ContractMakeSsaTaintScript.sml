(*
 * MakeSSA's first O1 run keeps the output's taint within the dead
 * bytes D: each output function runs in lockstep with its input
 * (makeSsaCurrentLockstep), and o1FrameLockstep carries taint_within over
 * such a context.
 *)
Theory o1ContractMakeSsaTaint
Ancestors
  o1PassContract ptrDiscipline unitMemInv venomPassSchedule list makeSsaCurrentLockstep
  makeSsaCurrentSim o1ContractMakeSsaReplay o1PassLift o1FrameLockstep unitTransformDefs

Theorem make_ssa_stage_taint:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions ==>
    taint_within D C' vs
Proof
  rpt strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `taint_within D C vs` by gvs[o1_src_inv_def] >>
  `C'.ctx_entry = C.ctx_entry /\
   LIST_REL (\fn fn'. ?t t'.
     ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
     make_ssa_current_fn t fn = (fn',t'))
     C.ctx_functions C'.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >> simp[] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     rpt strip_tac >> gvs[] >> drule make_ssa_pass_step_replay >> simp[]) >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions` by
    metis_tac[LIST_REL_LENGTH] >>
  `!n. n < LENGTH C.ctx_functions ==>
     make_ssa_input_ok (EL n C.ctx_functions) /\
     fn_inst_wf (EL n C.ctx_functions) /\
     wf_function (EL n C.ctx_functions) /\
     first_block_no_preds (EL n C.ctx_functions) /\
     first_block_no_phi (EL n C.ctx_functions) /\
     ?t t'. ir_supply_covers_fn t (EL n C.ctx_functions) /\
       ir_supply_inst_ok t /\
       make_ssa_current_fn t (EL n C.ctx_functions) =
         (EL n C'.ctx_functions,t')` by
    (rpt strip_tac >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
     `o1_fn_shape C (EL n C.ctx_functions) /\
      make_ssa_input_ok (EL n C.ctx_functions)` by
       metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
     gvs[o1_fn_shape_def, LIST_REL_EL_EQN]) >>
  `!n. n < LENGTH C.ctx_functions ==>
     fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     irule make_ssa_current_fn_fn_bisim >> gvs[make_ssa_input_ok_def] >>
     metis_tac[]) >>
  `ctx_bisim C C'` by
    (irule fn_bisim_ctx_bisim >> simp[LIST_REL_EL_EQN]) >>
  `lockstep_ctx (\fn fn' pos. T) vs.vs_labels C C'` by
    (simp[lockstep_ctx_def, LIST_REL_EL_EQN] >> rpt strip_tac >>
     `fn_bisim (EL n C.ctx_functions) (EL n C'.ctx_functions)` by
       metis_tac[] >>
     fs[fn_bisim_def] >>
     first_x_assum drule >> strip_tac >>
     qexists `make_ssa_pos (EL n C.ctx_functions) (EL n C'.ctx_functions)` >>
     irule make_ssa_current_fn_frame_lockstep >> metis_tac[]) >>
  drule_all taint_within_lockstep >> simp[]
QED
