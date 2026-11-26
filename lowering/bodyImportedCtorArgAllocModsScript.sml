(* Allocation bounds for an imported constructor selected by deployment lowering. *)
Theory bodyImportedCtorArgAllocMods
Ancestors
  compileUnit

Theorem selected_imported_ctor_alloc_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bytecode = SOME unit /\
  classify_functions_unit mods exps = (exts, int_fns, fb, ctor, imp_ctors) /\
  MEM f imp_ctors ==>
  fn_allocs_ok_unit mods f
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def, AllCaseEqs(), listTheory.EVERY_MEM] >>
  metis_tac[]
QED
