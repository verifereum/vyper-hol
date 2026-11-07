Theory ctorDeployMemoryRunMemEntryRegisterEnv
Ancestors
  moduleLowering context compileEnv finite_map list

Theorem ctor_register_constructor_env_fields:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv',st') ==>
    cenv'.ce_is_ctor = cenv.ce_is_ctor /\
    cenv'.ce_imm_alloca = cenv.ce_imm_alloca /\
    cenv'.ce_return_buf = cenv.ce_return_buf
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once compile_register_constructor_args_def] >- metis_tac[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >- metis_tac[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED
