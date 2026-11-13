Theory readonlyInvokeCopyFwdExecutionAbortTransfer
Ancestors
  readonlyInvokeCopyFwdExecutionAborts
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecutionAssertions
  readonlyInvokeCopyFwdExecutionControl readonlyInvokeCopyFwdStepsAborts
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdRel
  o1LowerDloadOccurrence o1LowerDloadGhost o1LowerDloadPtrDiscipline
  ptrDiscipline taintAgree frameViewFacts frameRelocationGuardedValues
  contextCodegenRel pointerConfinedDefs memLocDefs opcodeClass
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst
  list finite_map words

Theorem ricf_abort_frame_observations[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_returndata = t.vs_returndata /\
  (!op. IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  conj_tac
  >- (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
      drule taint_agree_frame >>
      disch_then (mp_tac o Q.AP_TERM `\st. st.vs_call_ctx`) >>
      simp[ricf_opaque_view_def]) >>
  conj_tac
  >- (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
      drule taint_agree_frame >>
      disch_then (mp_tac o Q.AP_TERM `\st. st.vs_returndata`) >>
      simp[ricf_opaque_view_def]) >>
  metis_tac[ricf_opaque_frame_operand_defined]
QED

Theorem ricf_abort_scalar[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [RETURNDATACOPY;CREATE;CREATE2;CALL] /\
  MEM op inst.inst_operands /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  Cases_on `eval_operand op s`
  >- (drule ricf_abort_frame_observations >> strip_tac >>
      qpat_x_assum `!op. IS_SOME _ <=> _` (qspec_then `op` mp_tac) >>
      Cases_on `eval_operand op t` >> simp[]) >>
  rename1 `eval_operand op s = SOME x` >>
  `eval_operand op t = SOME x` by
    (drule ricf_execution_nonaddress_operand >> disch_then irule >>
     fs[MEM] >> simp[is_pointer_preserving_op_def] >> metis_tac[]) >> simp[]
QED

Theorem ricf_abort_observer[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [RETURNDATACOPY;CREATE;CREATE2] /\
  (MEM inst.inst_opcode [CREATE;CREATE2] ==> ~s.vs_call_ctx.cc_static) /\
  step_inst fuel C inst s = Abort reason u ==>
  ?v. step_inst fuel Ct inst t = Abort reason v
Proof
  strip_tac >> drule ricf_abort_frame_observations >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `step_inst_base inst s = Abort reason u` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = RETURNDATACOPY`
  >- (`?dst off sz. inst.inst_operands = [dst;off;sz]` by
        gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      `eval_operand off s = eval_operand off t /\
       eval_operand sz s = eval_operand sz t` by
        (conj_tac >> drule ricf_abort_scalar >> disch_then irule >>
         simp[MEM, mem_read_ops_def, mem_write_ops_def] >>
         rpt CASE_TAC >> gvs[] >> metis_tac[]) >>
      mp_tac (Q.INST [`t` |-> `t`, `dst` |-> `dst`, `off` |-> `off`, `sz` |-> `sz`]
        ricf_returndatacopy_abort) >> (impl_tac >- simp[]) >> strip_tac >>
      qexists_tac `v` >> fs[step_inst_non_invoke]) >>
  Cases_on `inst.inst_opcode = CREATE`
  >- (`~s.vs_call_ctx.cc_static` by fs[MEM] >>
      `?value off sz. inst.inst_operands = [value;off;sz]` by
        gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
      `eval_operand sz s = eval_operand sz t` by
        (drule ricf_abort_scalar >> disch_then irule >>
         simp[MEM, mem_read_ops_def, mem_write_ops_def] >>
         rpt CASE_TAC >> gvs[] >> metis_tac[]) >>
      mp_tac (Q.INST [`t` |-> `t`, `value` |-> `value`, `off` |-> `off`, `sz` |-> `sz`]
        ricf_create_abort) >> (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      qexists_tac `v` >> fs[step_inst_non_invoke]) >>
  `inst.inst_opcode = CREATE2 /\ ~s.vs_call_ctx.cc_static` by fs[MEM] >>
  `?value off sz salt. inst.inst_operands = [value;off;sz;salt]` by
    gvs[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_abort_iff] >>
  `eval_operand sz s = eval_operand sz t` by
    (drule ricf_abort_scalar >> disch_then irule >>
     simp[MEM, mem_read_ops_def, mem_write_ops_def] >>
     rpt CASE_TAC >> gvs[] >> metis_tac[]) >>
  mp_tac (Q.INST [`t` |-> `t`, `value` |-> `value`, `off` |-> `off`,
    `sz` |-> `sz`, `salt` |-> `salt`] ricf_create2_abort) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `v` >> fs[step_inst_non_invoke]
QED

Theorem ricf_abort_call[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = CALL /\ step_inst fuel C inst s = Abort reason u ==>
  ?v. step_inst fuel Ct inst t = Abort reason v
Proof
  strip_tac >> drule ricf_abort_frame_observations >> strip_tac >>
  `?gas addr value ao sz ro rs.
    inst.inst_operands = [gas;addr;value;ao;sz;ro;rs]` by
    gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `eval_operand value s = eval_operand value t` by
    (mp_tac (Q.INST [`op` |-> `value`, `lo` |-> `lo`] ricf_abort_scalar) >>
     (impl_tac >- (simp[Excl "FILTER", MEM, mem_read_ops_def, mem_write_ops_def] >>
       rpt strip_tac >> gvs[Excl "FILTER"] >>
       qpat_x_assum `FILTER _ _ = [_]` mp_tac >> simp[FILTER] >>
       rpt (IF_CASES_TAC >> simp[]))) >> simp[]) >>
  qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(),
    exec_call_helpers_no_halt_abort] >>
  strip_tac >> gvs[] >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY] >> rpt conj_tac >>
     metis_tac[optionTheory.IS_SOME_DEF]) >>
  qpat_x_assum `IS_SOME (eval_operands _ t)` mp_tac >>
  simp[eval_operands_IS_SOME_EVERY, optionTheory.IS_SOME_EXISTS] >>
  rpt strip_tac >> gvs[step_inst_non_invoke,
    step_inst_base_opcode_eqs]
QED

Theorem ricf_execution_noninvoke_abort:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Abort reason u ==>
  ?v. step_inst fuel Ct inst t = Abort reason v
Proof
  strip_tac >>
  Cases_on `s.vs_call_ctx.cc_static /\
    MEM inst.inst_opcode [SSTORE;TSTORE;LOG;SELFDESTRUCT;CREATE;CREATE2]`
   >- (qpat_x_assum `s.vs_call_ctx.cc_static /\ _` strip_assume_tac >>
       `IS_SOME (eval_operands inst.inst_operands s) /\
       reason = ExHalt_abort` by
        (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >> fs[MEM] >>
         gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(),
           eval_operands_def, exec_result_helpers_no_halt_abort] >>
         rpt strip_tac >> gvs[eval_operands_def]) >>
      mp_tac (Q.INST [`Ct` |-> `Ct`, `fuel` |-> `fuel`,
        `rt` |-> `tn`, `ledger` |-> `certificates`]
        ricf_execution_static_effect_abort) >>
      (impl_tac >- simp[]) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [RETURNDATACOPY;CREATE;CREATE2]`
  >- (`MEM inst.inst_opcode [CREATE;CREATE2] ==> ~s.vs_call_ctx.cc_static` by
        (fs[MEM] >> metis_tac[]) >>
      drule_all ricf_abort_observer >> disch_then (qspec_then `Ct` strip_assume_tac) >>
      metis_tac[]) >>
  Cases_on `inst.inst_opcode = CALL`
  >- (drule_all ricf_abort_call >> disch_then (qspec_then `Ct` strip_assume_tac) >>
      metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE]`
  >- (drule_all ricf_execution_assert_abort >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `MEM inst.inst_opcode [REVERT;INVALID]` by
    (drule step_inst_abort_opcodes >> fs[MEM] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = INVALID`
  >- (`reason = ExHalt_abort` by
        fs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
      qexists_tac `halt_state (set_returndata [] t)` >> gvs[] >>
      irule ricf_execution_invalid_abort >> simp[]) >>
  `inst.inst_opcode = REVERT` by fs[MEM] >>
  `reason = Revert_abort /\
   ?addr sz. inst.inst_operands = [addr;sz]` by
    (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  mp_tac (Q.INST [`Ct` |-> `Ct`, `fuel` |-> `fuel`, `s1` |-> `u`,
    `ledger` |-> `certificates`] ricf_execution_revert) >>
  (impl_tac >- simp[]) >> strip_tac >> metis_tac[]
QED

