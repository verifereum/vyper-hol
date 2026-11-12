Theory allocaBudgetMonotone
Ancestors
  allocaFrontierBound allocaBudgetProps venomExecSemantics venomState
  venomInst finite_map list pred_set arithmetic

Theorem remaining_alloca_budget_domain_mono:
  FDOM s.vs_allocas SUBSET FDOM t.vs_allocas ==>
  remaining_alloca_budget xs t <= remaining_alloca_budget xs s
Proof
  Induct_on `xs` >> simp[remaining_alloca_budget_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >>
  gvs[remaining_alloca_budget_def, SUBSET_DEF] >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]
QED

Theorem remaining_alloca_budget_member_debit:
  MEM ins xs /\ ins.inst_opcode = ALLOCA /\
  ins.inst_id NOTIN FDOM s.vs_allocas /\
  FDOM t.vs_allocas = ins.inst_id INSERT FDOM s.vs_allocas ==>
  alloca_size ins + remaining_alloca_budget xs t <=
    remaining_alloca_budget xs s
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ins = h`
  >- (gvs[] >>
      `remaining_alloca_budget xs t <= remaining_alloca_budget xs s` by
        (irule remaining_alloca_budget_domain_mono >> simp[]) >>
      gvs[remaining_alloca_budget_def]) >>
  `alloca_size ins + remaining_alloca_budget xs t <=
     remaining_alloca_budget xs s` by metis_tac[MEM] >>
  simp[remaining_alloca_budget_def] >> rpt IF_CASES_TAC >>
  gvs[remaining_alloca_budget_def] >> decide_tac
QED

Theorem actual_alloca_frontier_member_preserved:
  MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
  step_inst_base ins s = OK t /\ alloca_frontier_inv ctx fn site s ==>
  alloca_frontier_inv ctx fn site' t
Proof
  rpt strip_tac >> drule_all step_inst_base_alloca_effect >>
  Cases_on `ins.inst_id IN FDOM s.vs_allocas` >> simp[] >> strip_tac
  >- (`remaining_alloca_budget (fn_insts fn) t =
       remaining_alloca_budget (fn_insts fn) s` by
        (irule remaining_alloca_budget_domain_cong >> simp[]) >>
      gvs[alloca_frontier_inv_def]) >>
  drule_all remaining_alloca_budget_member_debit >> strip_tac >>
  gvs[alloca_frontier_inv_def] >> decide_tac
QED
