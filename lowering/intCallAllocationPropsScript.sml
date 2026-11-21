(* Successful linked-unit lowering checks every selected internal allocation. *)
Theory intCallAllocationProps
Ancestors
  bodyInvSplit compileUnit list

Theorem contract_inv_internal_allocs:
  contract_inv mods exps ctx cenv cx /\
  MEM f (FST (SND (classify_functions_unit mods exps))) ==>
  fn_allocs_ok_unit mods f
Proof
  strip_tac >>
  qpat_x_assum `contract_inv _ _ _ _ _` mp_tac >>
  simp[contract_inv_def] >> strip_tac >>
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit mods exps = (exts,rest)` >>
  PairCases_on `rest` >> Cases_on `cx.in_deploy` >> gvs[] >>
  qmatch_asmsub_rename_tac `MEM f internals`
  >- (qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
      simp[lower_vyper_deploy_unit_mods_def, EVERY_MEM] >>
      rpt (pairarg_tac >> gvs[]) >>
      rw[] >> res_tac)
  >- (qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
      simp[lower_vyper_runtime_unit_mods_def, EVERY_MEM] >>
      rpt (pairarg_tac >> gvs[]) >>
      rw[] >> res_tac)
QED
