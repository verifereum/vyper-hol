(* Raw deployment label checks for a linked compilation unit. *)
Theory linkedDeployLabelReadiness
Ancestors
  compileUnit compileVyper compileEnv linkedRuntimeLabelReadiness
  deployLabelRunners runtimeLabelReadiness runtimeLabelInvariant
  venomInst list pair

Triviality constructor_package_unit_env_checks:
  rb_env_ok_for checks (FST (set_constructor_package_target target
    (package_constructor_unit mods T keys cf)))
Proof
  PairCases_on `cf` >>
  simp[package_constructor_unit_def, set_constructor_package_target_def,
       rb_build_compile_env_unit_for, rb_env_updates_for]
QED

Triviality internal_package_unit_env_checks:
  rb_env_ok_for checks (FST (SND (set_internal_package_target target
    (package_internal_fn_unit mods T keys T len f))))
Proof
  PairCases_on `f` >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def,
       rb_build_compile_env_unit_for, rb_env_updates_for]
QED

Theorem lower_vyper_deploy_unit_label_checks_mods:
  "runtime_begin" NOTIN FST checks /\
  lower_vyper_deploy_unit_mods mods exps rpolicy bytes = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  source_inst_ok checks inst
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> rpt strip_tac >>
  irule run_deploy_lowering_checks >> goal_assum (drule_at Any) >>
  qexists_tac `fn` >> simp[] >> irule generate_deploy_checks >> simp[] >>
  Cases_on `ctor_fn` >> gvs[set_constructor_package_target_def] >>
  conj_tac
  >- (qpat_x_assum `set_constructor_package_target _ _ = _`
        (mp_tac o Q.AP_TERM `FST`) >>
      simp[] >> disch_then (SUBST1_TAC o SYM) >>
      simp[constructor_package_unit_env_checks]) >>
  simp[EVERY_MAP, EVERY_MEM, ELIM_UNCURRY, internal_package_unit_env_checks]
QED
