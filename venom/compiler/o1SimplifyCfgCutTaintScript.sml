(* Cut-guarded request and halt taint through the SimplifyCFG trace.
   The gas cut is always tested at the reachable pre-step state. *)
Theory o1SimplifyCfgCutTaint
Ancestors
  o1SafeUpto o1ContractSimplifyCfgSrcFrame stateFrame venomState

Theorem scfg_context_trace_taint_within_upto:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  taint_within_upto D n C vs ==> taint_within_upto D n C' vs
Proof
  strip_tac >> simp[taint_within_upto_def] >> conj_tac
  >- (rpt strip_tac >>
      drule_all scfg_context_trace_live_frame_back >> strip_tac >>
      drule_all scfg_live_position_request_back >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      rename1 `frame_reachable vs C fs PG G tn f i src` >>
      `active_inst f i src` by metis_tac[scfg_frame_reachable_active] >>
      `gas_cut n vs src` by
        fs[gas_cut_def, scfg_data_agree_def, execution_frame_def,
           venom_state_component_equality] >>
      fs[taint_within_upto_def] >>
      first_x_assum drule_all >>
      fs[scfg_data_agree_def, execution_frame_def,
         venom_state_component_equality] >>
      metis_tac[]) >>
  rpt strip_tac >>
  drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  drule_all scfg_live_position_halt_back >>
  disch_then (qspec_then `C` strip_assume_tac) >> gvs[] >>
  rename1 `frame_reachable vs C fs PG G tn f inst src` >>
  rename1 `step_inst fuel C inst src = Halt out` >>
  `active_inst f inst src` by metis_tac[scfg_frame_reachable_active] >>
  `gas_cut n vs src` by
    fs[gas_cut_def, scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >>
  `step_taint inst src out tn = step_taint inst s s_h tn` by
    metis_tac[scfg_data_agree_step_taint] >>
  `ret_taint tn inst src = ret_taint tn inst s` by
    metis_tac[scfg_data_agree_ret_taint] >>
  fs[taint_within_upto_def] >>
  first_x_assum drule_all >>
  fs[scfg_data_agree_def, execution_frame_def,
     venom_state_component_equality]
QED
