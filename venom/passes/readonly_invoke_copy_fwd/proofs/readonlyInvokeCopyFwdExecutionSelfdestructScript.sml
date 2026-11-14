Theory readonlyInvokeCopyFwdExecutionSelfdestruct
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHeterogeneousLedger
  o1LowerDloadHaltResult o1LowerDloadShared o1LowerDloadOccurrence
  internalReturnCopyFwdSim pointerConfinedDefs frameRel
  ptrDiscipline taintAgree memLocDefs
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_selfdestruct_halt:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ taint_within D C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = SELFDESTRUCT /\
  step_inst fuel C inst s = Halt sh ==>
  ?th. step_inst fuel Ct inst t = Halt th /\ dead_result_rel D (Halt sh) (Halt th)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?beneficiary p. inst.inst_operands = [beneficiary] /\
    eval_operand beneficiary s = SOME p` by
    (qpat_x_assum `step_inst fuel C inst s = Halt sh` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `op_taint tn beneficiary = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand beneficiary t = SOME p` by
    (mp_tac (Q.INST [`op` |-> `beneficiary`, `x` |-> `p:256 word`,
       `rt` |-> `tn`] ricf_execution_nonaddress_operand) >>
     (impl_tac >- simp[is_pointer_preserving_op_def, mem_read_ops_def,
       mem_write_ops_def]) >> simp[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_call_ctx = t.vs_call_ctx` by
    (`ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
       sites (ricf_complete_params PG s.vs_params) G tn s t` by
       fs[ricf_execution_invariant_def] >>
     qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_shared >> drule taint_agree_call_ctx >>
     simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    simp[] >>
  `final_taint vs C sh (step_taint inst s sh tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >>
     qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`fuel`] >> simp[]) >>
  `(step_taint inst s sh tn).t_stor SUBSET
      D.d_stor sh.vs_call_ctx.cc_address
        (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
   (step_taint inst s sh tn).t_trans SUBSET
      D.d_trans sh.vs_call_ctx.cc_address (sh.vs_transient sh.vs_call_ctx.cc_address) /\
   (step_taint inst s sh tn).t_imm SUBSET D.d_imm sh.vs_immutables` by
    (fs[taint_within_def] >> metis_tac[]) >>
  drule_all ld_shared_selfdestruct_step >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  rename1 `step_inst fuel Ct inst t = Halt th` >>
  qexists_tac `th` >> simp[] >>
  irule ld_shared_halt_result >> gvs[] >>
  conj_tac >- (qexists_tac `{}` >> simp[]) >>
  qexistsl_tac [`sh.vs_call_ctx.cc_address`,`step_taint inst s sh tn`] >> simp[]
QED
