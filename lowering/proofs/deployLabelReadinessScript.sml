(* Raw deployment instruction checks allow the epilogue's runtime_begin copy. *)
Theory deployLabelReadiness
Ancestors
  deployLabelRunners runtimeLabelReadiness runtimeLabelInvariant
  compileVyper compileEnv venomInst list

Theorem constructor_package_env_checks[local]:
  !tops target keys cf.
    rb_env_ok_for checks (FST (set_constructor_package_target target
      (package_constructor tops T keys cf)))
Proof
  rpt gen_tac >> PairCases_on `cf` >>
  simp[package_constructor_def, set_constructor_package_target_def,
       rb_build_compile_env_for, rb_env_updates_for]
QED

Theorem internal_package_env_checks[local]:
  !tops target keys len f.
    rb_env_ok_for checks (FST (SND (set_internal_package_target target
      (package_internal_fn tops T keys T len f))))
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       rb_build_compile_env_for, rb_env_updates_for]
QED

Theorem lower_vyper_deploy_unit_label_checks:
  "runtime_begin" NOTIN FST checks /\
  lower_vyper_deploy_unit tops rpolicy bytes = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  source_inst_ok checks inst
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  irule run_deploy_lowering_checks >> goal_assum (drule_at Any) >>
  qexists_tac `fn` >> simp[] >> irule generate_deploy_checks >> simp[] >>
  Cases_on `ctor_fn` >> gvs[set_constructor_package_target_def] >>
  conj_tac
  >- (qpat_x_assum `set_constructor_package_target _ _ = _`
        (mp_tac o Q.AP_TERM `FST`) >>
      simp[] >> disch_then (SUBST1_TAC o SYM) >>
      simp[constructor_package_env_checks]) >>
  simp[EVERY_MAP, EVERY_MEM, pairTheory.ELIM_UNCURRY, internal_package_env_checks]
QED
