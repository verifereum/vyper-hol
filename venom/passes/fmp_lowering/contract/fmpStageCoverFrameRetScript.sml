(* Return coverage from a restored related source point.
   The backward/forward return contracts provide the source step and its
   image; source frame reachability, not merging callee state, proves the
   resumed caller is not halted. *)
Theory fmpStageCoverFrameRet
Ancestors
  fmpStageCoverInv fmpStageCoverCall fmpStageFmpSteps fmpStageOpBase
  fmpStageRel ptrDiscipline o1PassContract contextCodegenRel
  lowerDloadPtrRawReachable o1ContractSimplifyCfgSrcFrame o1PassLift
  simplifyCfgAvailability unitTransformDefs passSimulationDefs venomExecSemantics venomState
  venomInst venomWf finite_map words list pred_set
Libs
  pairLib

Theorem fmp_cov_ret_point:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' (g::stk') PG' G' tn' fn' ri t /\
  active_inst fn' ri t /\
  frame_reachable vs C stk PG G tn fn ri s /\ active_inst fn ri s /\
  ~s.vs_halted /\ ri.inst_opcode = RET /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts (g::stk') /\
  step_inst fuel C' ri t = IntRet ret t_end /\
  bind_outputs g.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state g.cf_state t_end)) = SOME t' /\
  active_inst g.cf_fn ti' (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ==>
  ?stk0 PG0 G0 tn0 fn0 inst0 s0 sm0 lo0 ts0.
    frame_reachable vs C stk0 PG0 G0 tn0 fn0 inst0 s0 /\
    active_inst fn0 inst0 s0 /\ ~s0.vs_halted /\
    fmp_stage_rel D C' sm0 (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk0 PG0 G0 tn0 fn0 s0 lo0
      (t' with vs_inst_idx := SUC g.cf_state.vs_inst_idx) ts0 /\
    lookup_function fn0.fn_name C'.ctx_functions = SOME g.cf_fn /\
    fmp_cov_stack C' stk0 ts0 stk'
Proof
  rpt strip_tac >>
  Cases_on `stk` >> fs[fmp_cov_stack_def] >>
  Cases_on `ts` >> fs[fmp_cov_stack_def] >>
  rename1 `fmp_cov_stack C' (f::fs) (p::ps) (g::stk')` >>
  PairCases_on `p` >> gvs[fmp_cov_stack_def] >>
  drule_all (SRULE [] (Q.INST [`k` |-> `0`,
    `fmp0` |-> `w2n vs'.vs_initial_fmp`, `raw0` |-> `w2n fmp`]
    fmp_stage_back_ret)) >>
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`k` |-> `0`, `rinst'` |-> `ri`,
    `fmp0` |-> `w2n vs'.vs_initial_fmp`, `raw0` |-> `w2n fmp`]
    fmp_stage_invoke_return)) >>
  strip_tac >>
  qpat_x_assum `!k'. step_inst _ _ _ _ = _` (qspec_then `fuel` assume_tac) >>
  gvs[] >>
  `frame_reachable vs C fs f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> metis_tac[]) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `ivk' = g.cf_inst` by
    (drule_all active_inst_block_lookup >> strip_tac >>
     `?bb. lookup_block g.cf_state.vs_current_bb g.cf_fn.fn_blocks = SOME bb /\
           get_instruction bb g.cf_state.vs_inst_idx = SOME g.cf_inst` by
       metis_tac[active_inst_block_lookup] >> gvs[]) >>
  gvs[] >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
   !nm h. lookup_function nm C.ctx_functions = SOME h ==> wf_function h` by
    (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
        o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  drule supply_frame_reach_not_halted >>
  fs[fn_entry_state_def] >> strip_tac >>
  qexistsl [`fs`, `f.cf_params`,
    `DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs))`,
    `tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs))`,
    `f.cf_fn`, `inst'`, `s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx`,
    `DRESTRICT sm {key | FST key < w2n f.cf_state.vs_fmp}`, `p1`, `ps`] >>
  simp[]
QED
