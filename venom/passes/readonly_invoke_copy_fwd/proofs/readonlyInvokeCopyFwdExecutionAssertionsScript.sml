Theory readonlyInvokeCopyFwdExecutionAssertions
Ancestors
  readonlyInvokeCopyFwdExecutionOrdinary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadJointIdentity o1LowerDloadOccurrence o1LowerDloadGhost
  o1PassContract unitShapeDefs ptrDiscipline pointerConfinedDefs memLocDefs
  taintAgree contextCodegenRel venomWf venomExecSemantics venomExecProps
  venomState venomInst list finite_map words

Theorem ricf_execution_assert_operand[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
  MEM cond inst.inst_operands /\ eval_operand cond s = SOME x ==>
  eval_operand cond t = SOME x
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn cond = {}` by
    (spose_not_then assume_tac >> fs[taint_ok_def] >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `cond` mp_tac) >>
     gvs[MEM]) >>
  `~is_pointer_preserving_op inst.inst_opcode /\
   ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE;RET;RETFMP;DRET] /\
   mem_read_ops inst = NONE /\ mem_write_ops inst = NONE` by
    fs[MEM, is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  drule_all ricf_execution_scalar_operand >> simp[]
QED

Theorem ricf_execution_assert_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  o1_fn_shape C fn /\ wf_ssa fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `ssa_form fn /\ opaque_use_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_ssa_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `?cond x. inst.inst_operands = [cond] /\ eval_operand cond s = SOME x /\
      x <> 0w /\ u = s` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      AllCaseEqs()] >> metis_tac[]) >>
  `eval_operand cond t = SOME x` by
    (irule ricf_execution_assert_operand >> simp[] >> metis_tac[MEM]) >>
  `step_prov PG G inst s = G /\ occurrence_step a HP H inst s = H /\
   step_taint inst s s tn = tn` by
    (irule ld_joint_identity_annotations >> fs[MEM]) >>
  qpat_x_assum `u = s` SUBST_ALL_TAC >> qexists_tac `t` >> conj_tac
  >- (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  mp_tac (Q.INST [`u` |-> `s`, `v` |-> `t`, `rt` |-> `tn`]
    ricf_execution_next) >>
  impl_tac >- (fs[MEM, is_terminator_def, occurrence_sites_step_def,
    ricf_execution_invariant_def] >> gvs[]) >> simp[]
QED

Theorem ricf_execution_assert_abort:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ssa_form fn /\ opaque_use_ok fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = Abort reason u ==>
  ?v. step_inst fuel Ct inst t = Abort reason v
Proof
  strip_tac >>
  `?cond. inst.inst_operands = [cond] /\ eval_operand cond s = SOME 0w` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      AllCaseEqs()] >> metis_tac[]) >>
  `eval_operand cond t = SOME 0w` by
    (irule ricf_execution_assert_operand >> simp[] >> metis_tac[MEM]) >>
  fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED
