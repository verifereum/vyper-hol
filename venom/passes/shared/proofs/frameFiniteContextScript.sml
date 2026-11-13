Theory frameFiniteContext
Ancestors frameFiniteExecution venomInstProofs1 venomExecProofs calleeTransport
  venomExecSemantics venomState venomInst opcodeClass

Theorem step_inst_base_OK_call_ctx:
  step_inst_base inst s = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem step_inst_base_IntRet_call_ctx:
  step_inst_base inst s = IntRet ret t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_preserves_non_memory >> simp[]
QED

Theorem finite_execution_call_ctx:
  (!C i s r. finite_step C i s r ==>
    (!t. r = OK t ==> t.vs_call_ctx = s.vs_call_ctx) /\
    (!ret t. r = IntRet ret t ==> t.vs_call_ctx = s.vs_call_ctx)) /\
  (!C bb s r. finite_block C bb s r ==>
    (!t. r = OK t ==> t.vs_call_ctx = s.vs_call_ctx) /\
    (!ret t. r = IntRet ret t ==> t.vs_call_ctx = s.vs_call_ctx)) /\
  (!C fn s r. finite_run C fn s r ==>
    (!t. r = OK t ==> t.vs_call_ctx = s.vs_call_ctx) /\
    (!ret t. r = IntRet ret t ==> t.vs_call_ctx = s.vs_call_ctx))
Proof
  ho_match_mp_tac finite_step_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[step_inst_base_OK_call_ctx, step_inst_base_IntRet_call_ctx])
  >- (rpt strip_tac >> gvs[] >>
      mp_tac (Q.ISPEC `\(st:venom_state). st.vs_call_ctx` bind_outputs_preserves) >>
      simp[update_var_def] >> disch_then drule >>
      Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[AllCaseEqs()])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => fs[Once th]))
  >- (rpt strip_tac >> gvs[])
  >> rpt strip_tac >> drule eval_phis_only_updates_vs_vars >>
     disch_then (fn th => fs[Once th])
QED

Theorem finite_step_OK_call_ctx:
  finite_step C i s (OK t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_step_IntRet_call_ctx:
  finite_step C i s (IntRet ret t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_block_OK_call_ctx:
  finite_block C bb s (OK t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_block_IntRet_call_ctx:
  finite_block C bb s (IntRet ret t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_run_OK_call_ctx:
  finite_run C fn s (OK t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_run_IntRet_call_ctx:
  finite_run C fn s (IntRet ret t) ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[finite_execution_call_ctx]
QED

Theorem finite_callee_IntRet_address:
  setup_callee fn args caller = SOME cs /\
  finite_run C fn cs (IntRet ret send) ==>
  send.vs_call_ctx.cc_address = caller.vs_call_ctx.cc_address
Proof
  strip_tac >> drule finite_run_IntRet_call_ctx >>
  drule setup_callee_shared_fields >> simp[]
QED
