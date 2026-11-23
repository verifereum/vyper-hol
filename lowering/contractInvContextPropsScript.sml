Theory contractInvContextProps
Ancestors
  bodyInvSplit compileUnit vyperCompiler alist

Theorem contract_inv_singleton_source_modules:
  contract_inv [(NONE,tops)] [] ctx cenv cx ==>
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]
Proof
  simp[contract_inv_def]
QED

Theorem contract_inv_lowering_context:
  contract_inv mods exps ctx cenv cx ==> lowering_context_ok ctx
Proof
  simp[contract_inv_def] >> strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
      simp[lower_vyper_deploy_unit_mods_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      strip_tac >>
      qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[run_deploy_lowering_def] >>
      pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> strip_tac >>
  imp_res_tac run_grouped_lowering_context >>
  imp_res_tac run_lowering_context_ok >> simp[]
QED
