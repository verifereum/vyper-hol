(* Allocation resources for successful straight-line sequences. *)
Theory bodyIntCallFamStmtLogSuffixResources
Ancestors
  intCallFrame allocaBudgetProps venomMemProofs exprLoweringProps
  venomExecSemantics venomState list arithmetic

Theorem intcall_noninvoke_step_resources:
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t /\
  allocas_above lo s ==>
  allocas_above lo t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> conj_tac
  >- (`step_inst 0 ARB inst s = OK t` by
        (once_rewrite_tac[step_inst_def] >> simp[]) >>
      drule_all step_inst_allocas_above >>
      disch_then (qspecl_then [`0`,`ARB`,`inst`] mp_tac) >>
      simp[result_allocas_above_def]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule_all step_inst_base_alloca_effect >>
      Cases_on `inst.inst_id IN FDOM s.vs_allocas` >> simp[]) >>
  qspecl_then [`inst`,`s`,`t`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >> simp[]
QED

Theorem intcall_noninvoke_run_resources:
  !code s t. run_inst_seq code s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE) code /\ allocas_above lo s ==>
    allocas_above lo t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all intcall_noninvoke_step_resources >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
