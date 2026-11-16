Theory loweringBudgetAbortFrontier
Ancestors
  loweringCallBudgetHistory venomExecSemantics venomInstProofs1
  contextCodegenRel list

Theorem budget_path_assert_zero[local]:
  !checked cfg p h marks q.
    lower_budget_path checked cfg p h marks q ==>
    !i op.
      active_inst p.bp_fn i p.bp_state /\
      (!j. active_inst p.bp_fn j p.bp_state ==> j = i) /\
      i.inst_opcode = ASSERT /\ i.inst_operands = [op] /\
      eval_operand op p.bp_state = SOME 0w ==>
      h = [] /\ marks = [] /\ q = p
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  rename1 `ai.inst_opcode = ASSERT` >>
  first_x_assum (qspecl_then [`ai`, `op`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[Once step_inst_def, step_inst_base_opcode_eqs]
QED

Theorem lower_budget_path_assert_zero:
  !checked D lo explicit ctx p i op h marks q.
    active_inst p.bp_fn i p.bp_state /\
    (!j. active_inst p.bp_fn j p.bp_state ==> j = i) /\
    i.inst_opcode = ASSERT /\ i.inst_operands = [op] /\
    eval_operand op p.bp_state = SOME 0w /\
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q ==>
    h = [] /\ marks = [] /\ q = p
Proof
  metis_tac[budget_path_assert_zero]
QED
