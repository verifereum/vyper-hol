Theory dftGasInvOracleFrame
Ancestors
  dftGasOracleDefs dftGasInvPrefixRun dftRunRel venomInstProofs1
  venomExecSemantics venomInst venomState contextCodegenRel list

Theorem inv_fold_update_var_call_ctx[local]:
  !s. (FOLDL (\s (x,v). update_var x v s) s xs).vs_call_ctx = s.vs_call_ctx
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >>
  rename1 `((\(x,v). update_var x v s) pair).vs_call_ctx = _` >>
  PairCases_on `pair` >> simp[]
QED

Theorem inv_bind_outputs_call_ctx:
  bind_outputs outs vals s = SOME t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[bind_outputs_def] >> strip_tac >>
  gvs[AllCaseEqs(), inv_fold_update_var_call_ctx]
QED

Theorem inv_base_terminator_call_ctx[local]:
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def] >> pairarg_tac >> gvs[]
QED

Theorem inv_base_call_ctx:
  step_inst_base inst s = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[inv_base_terminator_call_ctx] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem inv_ev_step_call_ctx:
  ev_step orc p d fuel ctx inst s = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[Once ev_step_def] >> Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_gas_def] >> strip_tac >> gvs[AllCaseEqs()]) >>
  simp[] >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
      rename1 `bind_outputs _ ret.iret_values _ = SOME _` >>
      drule inv_bind_outputs_call_ctx >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  simp[] >> metis_tac[inv_base_call_ctx]
QED

Theorem inv_ev_prefix_call_ctx:
  !n s t. inv_ev_prefix orc p d ctx bb n s t ==>
    t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  drule inv_ev_step_call_ctx >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inv_ev_prefix_nonstatic:
  inv_ev_prefix orc p d ctx bb n s t /\ ~s.vs_call_ctx.cc_static ==>
  ~t.vs_call_ctx.cc_static
Proof
  metis_tac[inv_ev_prefix_call_ctx]
QED

Theorem inv_enters_block_call_ctx:
  enters_block fn s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  rw[enters_block_def] >> drule dft_eval_phis_call_ctx >> simp[]
QED

Theorem inv_setup_callee_call_ctx:
  setup_callee fn args s = SOME t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()]
QED

Theorem inv_ev_reachable_call_ctx:
  !orc s ctx p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
    t.vs_call_ctx = s.vs_call_ctx
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt strip_tac
  >- (drule inv_enters_block_call_ctx >> simp[])
  >- (drule inv_ev_step_call_ctx >> gvs[])
  >- (drule inv_ev_step_call_ctx >> drule inv_enters_block_call_ctx >> gvs[])
  >> drule inv_setup_callee_call_ctx >> drule inv_enters_block_call_ctx >> gvs[]
QED

Theorem inv_ev_reachable_nonstatic:
  ev_reachable orc s ctx p d fn inst t /\ ~s.vs_call_ctx.cc_static ==>
  ~t.vs_call_ctx.cc_static
Proof
  metis_tac[inv_ev_reachable_call_ctx]
QED
