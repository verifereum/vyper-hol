(*
 * The layout chain's pointer and taint invariants, cut at a gas reading.
 *
 * ptr_discipline and taint_within quantify over every frame_reachable
 * state of a run, so a run cut at its n-th GAS event can't supply them.
 * Their guarded forms ask only for states that have consumed fewer than
 * n gas readings (gas_cut).  The layout chain consults them at the
 * configurations of one joint trace, and gas readings only shrink along
 * a trace, so gas_cut at the trace's end gives it at every configuration
 * on the trace (trace_config_gas_cut).  layout_cut_safe bundles the
 * guarded invariants with gas_cut at the trace's end.
 *
 * With n = SUC (LENGTH vs0.vs_gas_readings) gas_cut always holds, so the
 * whole-run invariants give layout_cut_safe (layout_cut_safe_whole_run).
 *)
Theory concretizeLayoutCutSafe
Ancestors
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  o1SafeUpto ptrDiscipline ptrSafeRun contextCodegenRel gasOracleReplay gasCount
  stateEquiv venomExecSemantics venomState venomInst list arithmetic

(* ===== Gas readings only shrink ===== *)

Theorem gas_cut_readings_mono:
  gas_cut n vs t /\ LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings ==>
  gas_cut n vs s
Proof
  simp[gas_cut_def]
QED

Theorem step_inst_noninvoke_readings_le:
  inst.inst_opcode <> INVOKE /\
  (step_inst fuel ctx inst s = OK t \/ step_inst fuel ctx inst s = IntRet v t) ==>
  LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings
Proof
  strip_tac >> gvs[step_inst_non_invoke] >> (
  Cases_on `inst.inst_opcode = GAS`
  >- gvs[step_inst_base_def, exec_gas_def, AllCaseEqs()] >>
  `gas_replay_at 0 (step_inst_base inst) s` by simp[gas_base_non_gas] >>
  `s with vs_gas_readings := s.vs_gas_readings = s` by
    simp[venom_state_component_equality] >>
  gvs[gas_replay_at_def] >>
  first_x_assum (qspec_then `s.vs_gas_readings` mp_tac) >>
  gvs[lift_result_def])
QED

Theorem enters_block_readings:
  enters_block fn s s1 ==> s1.vs_gas_readings = s.vs_gas_readings
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule gas_count_phis_ok >> simp[]
QED

Theorem return_readings_le:
  step_inst fuel ctx rinst s = IntRet ret s_end /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller s_end)) = SOME s' ==>
  LENGTH s'.vs_gas_readings <= LENGTH s.vs_gas_readings
Proof
  strip_tac >> drule step_inst_intret_not_invoke >> strip_tac >>
  drule gas_bind_outputs_readings >> simp[] >> strip_tac >>
  irule step_inst_noninvoke_readings_le >> metis_tac[]
QED

Definition joint_state_def:
  joint_state (JointConfig stk PG G tn fn inst s oms om hs h) = s
End

Theorem joint_transition_readings_le:
  joint_transition ctx q ev q' ==>
  LENGTH (joint_state q').vs_gas_readings <=
  LENGTH (joint_state q).vs_gas_readings
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[joint_state_def]
  >- (irule step_inst_noninvoke_readings_le >> metis_tac[])
  >- (drule enters_block_readings >> simp[] >> strip_tac >>
      irule step_inst_noninvoke_readings_le >>
      `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      metis_tac[])
  >- (drule enters_block_readings >> drule gas_setup_callee_readings >>
      simp[])
  >> metis_tac[return_readings_le]
QED

Theorem joint_chain_readings_le:
  !es q qs r. joint_chain ctx q es qs r ==>
    EVERY (\u. LENGTH (joint_state r).vs_gas_readings <=
               LENGTH (joint_state u).vs_gas_readings) (q::qs)
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[] >>
  strip_tac >> drule joint_transition_readings_le >> decide_tac
QED

Theorem trace_config_gas_cut:
  joint_trace vs0 C q0 es qs q /\ gas_cut n vs0 (joint_state q) /\
  k <= LENGTH es ==>
  gas_cut n vs0 (joint_state (EL k (q0::qs)))
Proof
  simp[joint_trace_def] >> strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_chain_length] >>
  drule joint_chain_readings_le >> rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `k` mp_tac) >> impl_tac >- gvs[] >>
  metis_tac[gas_cut_readings_mono]
QED

(* ===== The bundled premise ===== *)

Definition layout_cut_safe_def:
  layout_cut_safe D lo n vs0 C q <=>
    ptr_discipline_upto lo n C vs0 /\ taint_within_upto D n C vs0 /\
    gas_cut n vs0 (joint_state q) /\ alloca_frontier_upto n C vs0
End

Theorem layout_cut_safe_whole_run:
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ taint_within D C vs0 ==>
  layout_cut_safe D lo (SUC (LENGTH vs0.vs_gas_readings)) vs0 C q
Proof
  simp[layout_cut_safe_def, gas_cut_def, mem_inv_raw_alloca_frontier_upto,
       ptr_discipline_upto_whole, taint_within_upto_whole]
QED

(* A configuration on the trace is frame-reachable and inside the cut. *)
Theorem layout_cut_safe_frame:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k <= LENGTH es /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  frame_reachable vs0 C stk PG G tn fn inst s /\ gas_cut n vs0 s
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  conj_tac
  >- (drule joint_trace_prefix_reachable >> rewrite_tac[EVERY_EL] >>
      disch_then (qspec_then `k` mp_tac) >> impl_tac >- gvs[] >>
      gvs[joint_config_reachable_def] >>
      metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `gas_cut n vs0 (joint_state (EL k (q0::qs)))` by
    (irule trace_config_gas_cut >> qexistsl_tac [`C`, `es`, `qend`] >>
     fs[layout_cut_safe_def]) >>
  gvs[joint_state_def]
QED

(* The alloca frontier at a configuration on the trace fits a word. *)
Theorem layout_cut_safe_frontier:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k <= LENGTH es /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  s.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all layout_cut_safe_frame >>
  fs[layout_cut_safe_def, alloca_frontier_upto_def] >> metis_tac[]
QED

Theorem layout_cut_safe_edge_frame:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k < LENGTH es /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  frame_reachable vs0 C stk PG G tn fn inst s /\ gas_cut n vs0 s
Proof
  strip_tac >> `k <= LENGTH es` by decide_tac >>
  drule_all layout_cut_safe_frame >> simp[]
QED

Theorem ptr_discipline_upto_at:
  ptr_discipline_upto lo n C vs0 /\
  frame_reachable vs0 C stk PG G tn fn inst s /\ gas_cut n vs0 s ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s)
Proof
  simp[ptr_discipline_upto_def] >> metis_tac[]
QED

(* The per-state pointer facts at a configuration on the trace. *)
Theorem layout_cut_safe_ptr_at:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k <= LENGTH es /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s)
Proof
  strip_tac >> drule_all layout_cut_safe_frame >> strip_tac >>
  irule ptr_discipline_upto_at >> fs[layout_cut_safe_def] >> metis_tac[]
QED

Theorem layout_cut_safe_ptr_edge:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k < LENGTH es /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s)
Proof
  strip_tac >> `k <= LENGTH es` by decide_tac >>
  drule_all layout_cut_safe_ptr_at >> simp[]
QED

Theorem layout_cut_safe_ptr_cfg:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k < LENGTH (q0::qs) /\
  EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s)
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `k <= LENGTH es` by fs[] >>
  drule_all layout_cut_safe_ptr_at >> simp[]
QED

Theorem layout_cut_safe_frame_cfg:
  layout_cut_safe D lo n vs0 C qend /\ joint_trace vs0 C q0 es qs qend /\
  k < LENGTH (q0::qs) /\
  EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
  frame_reachable vs0 C stk PG G tn fn inst s /\ gas_cut n vs0 s
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `k <= LENGTH es` by fs[] >>
  drule_all layout_cut_safe_frame >> simp[]
QED

(* The request clause, at a request-growing step inside the cut. *)
Theorem taint_within_upto_request:
  taint_within_upto D n ctx vs /\
  frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
  tn.t_stor SUBSET
    D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET
    D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)
Proof
  strip_tac >> fs[taint_within_upto_def] >> first_x_assum drule_all >> simp[]
QED

(* The halt clause, at a halting step inside the cut. *)
Theorem taint_within_upto_halt:
  taint_within_upto D n ctx vs /\
  frame_reachable vs ctx stk PG G T0 fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = Halt s_h ==>
  (step_taint inst s s_h T0).t_stor SUBSET
    D.d_stor s_h.vs_call_ctx.cc_address
      (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
  (step_taint inst s s_h T0).t_trans SUBSET
    D.d_trans s_h.vs_call_ctx.cc_address
      (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
  (step_taint inst s s_h T0).t_imm SUBSET D.d_imm s_h.vs_immutables /\
  ret_taint T0 inst s SUBSET D.d_ret s_h.vs_returndata
Proof
  strip_tac >> fs[taint_within_upto_def] >> first_x_assum drule_all >> simp[]
QED
