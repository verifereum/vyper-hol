Theory simplifyCfgSimTools
Ancestors
  o1PassLift venomWf venomExecSemantics passSimulationDefs
  contextCodegenRel list

Theorem frame_result_rel_refl:
  terminates r /\ (!s. r <> OK s) ==> frame_result_rel r r
Proof
  Cases_on `r` >> simp[terminates_def, frame_result_rel_def]
QED

Theorem run_blocks_frame_result_refl:
  terminates (run_blocks fuel ctx fn s) ==>
  frame_result_rel (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn s)
Proof
  strip_tac >> irule frame_result_rel_refl >>
  simp[run_blocks_not_OK]
QED

Theorem mem_corr_refl:
  mem_corr inst s inst s
Proof
  simp[mem_corr_def]
QED

Theorem call_corr_trans:
  call_corr i1 s1 i2 s2 /\ call_corr i2 s2 i3 s3 ==>
  call_corr i1 s1 i3 s3
Proof
  pure_rewrite_tac[call_corr_def] >>
  Cases_on `i3.inst_opcode = INVOKE` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fn_bisim_refl:
  fn_bisim fn fn
Proof
  simp[fn_bisim_def] >> metis_tac[run_blocks_frame_result_refl]
QED

Theorem fn_bisim_trans:
  fn_bisim f1 f2 /\ fn_bisim f2 f3 ==> fn_bisim f1 f3
Proof
  simp[fn_bisim_def] >> rpt strip_tac >>
  gvs[fn_entry_state_def] >>
  metis_tac[frame_result_rel_trans, frame_result_rel_terminates]
QED

Theorem frame_sim_trans:
  frame_sim L C1 C2 f1 f2 /\ frame_sim L C2 C3 f2 f3 /\
  fn_entry_label f2 = fn_entry_label f1 ==>
  frame_sim L C1 C3 f1 f3
Proof
  rewrite_tac[frame_sim_def] >> rpt strip_tac >>
  `fn_entry_state f2 s0` by gvs[fn_entry_state_def] >>
  metis_tac[mem_corr_trans, call_corr_trans]
QED

Theorem active_inst_wf:
  fn_inst_wf fn /\ active_inst fn inst s ==> inst_wf inst
Proof
  rw[fn_inst_wf_def, active_inst_def] >>
  metis_tac[MEM_EL]
QED

Theorem call_corr_refl:
  inst_wf inst ==> call_corr inst s inst s
Proof
  simp[call_corr_def] >> strip_tac >> strip_tac >>
  gvs[inst_wf_def, decode_invoke_def]
QED

Theorem ctx_bisim_step_ok:
  ctx_bisim C C' /\ step_inst fuel C' inst s = OK t ==>
  ?fuel'. step_inst fuel' C inst s = OK t
Proof
  strip_tac >> drule (cj 2 ctx_bisim_step_inst) >>
  disch_then (qspecl_then [`fuel`, `inst`, `s`] mp_tac) >>
  simp[terminates_def] >> strip_tac >>
  rename1 `step_result_rel (step_inst n C inst s)` >>
  Cases_on `step_inst n C inst s` >>
  gvs[step_result_rel_def, frame_result_rel_def] >> metis_tac[]
QED

Theorem frame_reach_ctx_bisim:
  !C' fn s0 inst s. frame_reach C' fn s0 inst s ==>
  !C. ctx_bisim C C' ==> frame_reach C fn s0 inst s
Proof
  ho_match_mp_tac frame_reach_ind >> rpt strip_tac
  >- metis_tac[frame_reach_rules]
  >- metis_tac[ctx_bisim_step_ok, frame_reach_rules]
  >> metis_tac[ctx_bisim_step_ok, frame_reach_rules]
QED

Theorem frame_sim_ctx_bisim:
  ctx_bisim C C' /\ fn_inst_wf fn ==> frame_sim L C C' fn fn
Proof
  strip_tac >> simp[frame_sim_def] >> qx_genl_tac [`s0`, `j`, `t`] >> strip_tac >>
  qexistsl_tac [`j`, `t`] >>
  metis_tac[frame_reach_ctx_bisim, mem_corr_refl, call_corr_refl,
            frame_reach_active, active_inst_wf]
QED

Theorem ctx_bisim_refl:
  ctx_bisim C C
Proof
  simp[ctx_bisim_def] >> rpt strip_tac >>
  metis_tac[run_blocks_frame_result_refl]
QED
