(* Lowering succeeds only with the policy's MCOPY capability. *)
Theory bodyLoweringTargetProps
Ancestors
  bodyInvSplit compileUnit vyperCompiler

Theorem body_inv_mcopy_mods:
  contract_inv mods exps ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  simp[contract_inv_def, PULL_EXISTS] >> rpt strip_tac >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_mods_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[run_deploy_lowering_def, AllCaseEqs(), lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_mods_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[run_lowering_def, run_grouped_lowering_def, AllCaseEqs(), lowering_policy_ok_def]
QED
