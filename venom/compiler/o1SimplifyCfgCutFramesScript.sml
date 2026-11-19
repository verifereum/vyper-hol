(* SimplifyCFG transports pointer/frame observations at the same gas cut. *)
Theory o1SimplifyCfgCutFrames
Ancestors
  o1ContractSimplifyCfgSrcFrame o1SafeUpto stateFrame venomState

Theorem scfg_context_trace_frame_rows_upto:
  scfg_context_trace C C' /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  ptr_discipline_upto lo n C vs /\
  (ctx_has_dalloca C' ==> ctx_has_dalloca C) /\
  frame_reachable vs C' stk PG G tn g j t /\ gas_cut n vs t ==>
  access_ok lo G g j t /\ taint_ok g tn j t /\ allocas_from lo t /\
  (ctx_has_dalloca C' ==> allocas_below_fmp t)
Proof
  strip_tac >> drule_all scfg_context_trace_live_frame_back >> strip_tac >>
  `gas_cut n vs s` by
    fs[gas_cut_def, scfg_data_agree_def, execution_frame_def,
       venom_state_component_equality] >>
  `access_ok lo G f i s /\ taint_ok f tn i s /\ allocas_from lo s /\
   (ctx_has_dalloca C ==> allocas_below_fmp s)` by
    metis_tac[ptr_discipline_upto_def] >>
  metis_tac[scfg_live_position_access_ok, scfg_live_position_trace_taint,
            scfg_data_agree_allocas]
QED
