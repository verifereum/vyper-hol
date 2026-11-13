Theory deployOutcomesFreeDeploy
Ancestors
  deployOutcomesFreeEntry deployOutcomesFreeBody deployOutcomesFreeTransport
  ctorDeployLowering ctorDeployMemory ctorDeployDload compileVyper

Theorem deploy_entry_excludes_outcomes:
  deploy_source_ok tops am tx /\
  lower_vyper_deploy_unit tops rp bc = SOME u ==>
  ?name fn. u.cu_context.ctx_entry = SOME name /\
    lookup_function name u.cu_context.ctx_functions = SOME fn /\
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts fn)
Proof
  strip_tac >> irule lower_vyper_deploy_unit_entry_excludes_outcomes >>
  rpt (goal_assum (drule_at Any)) >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `ctor_named_init (SOME cf)` by
    (drule_all lower_vyper_deploy_unit_ctor_named_init >> simp[]) >>
  irule outcomes_free_constructor_body >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem deploy_result_outcomes_replace[simp]:
  deploy_venom_result_rel tops bc tx src
    (map_result_state (\t. t with vs_outcomes := os) r) =
  deploy_venom_result_rel tops bc tx src r
Proof
  Cases_on `r` >> simp[dftCommutationTheory.map_result_state_def,
    deployOutcomesFreeBoundaryTheory.deploy_venom_result_rel_outcomes_halt,
    deployOutcomesFreeBoundaryTheory.deploy_venom_result_rel_outcomes_abort] >>
  Cases_on `src` >> simp[ctorDeployDefsTheory.deploy_venom_result_rel_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[ctorDeployDefsTheory.deploy_venom_result_rel_def]
QED
