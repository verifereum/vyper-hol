Theory ctorDeployMemoryRunPtrPrefixEntrySemanticMods
Ancestors
  entryModuleLocations ctorDeployLoweringFrame entryLocals
  e2eDeployModsDefs compileUnit compileVyper compileEnv bodyInvSplit
  moduleLowering vyperTypeContract vyperTypeContractContext
  finite_map pair

Theorem deploy_ptr_ctor_environment_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME unit /\
  deploy_typing_ok_mods mods exps am tx /\
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  classify_functions_unit mods exps = (exts, ints, fb, SOME cf, imported_ctor_fns) /\
  set_constructor_package_target rpolicy.rpol_target
    (package_constructor_unit mods T (K global_nonreentrant_slot) cf) =
    (ce0,pos_args,payable,nr,key,ut,ctor_body,ret) /\
  cap = imm_len_mods mods /\
  compile_register_constructor_args
    (ce0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
    pos_args 0 0 st1 = (ce1,st2) /\
  ce = ce1 with ce_ctor_exit_label := SOME exit_lbl ==>
  immutable_section_layout_mods mods ce /\ ce.ce_module = NONE /\ ce.ce_is_ctor
Proof
  strip_tac >>
  drule_then strip_assume_tac deploy_frame_register_static_fields >>
  drule_then strip_assume_tac compile_register_constructor_args_fields >>
  sg `ce0.ce_module = NONE /\ ce0.ce_is_ctor /\
      ce0.ce_module_vars =
        add_immutable_locations_unit
          (get_struct_fields (make_struct_fields_map_mods mods)) mods
          (add_module_var_locations_mods mods FEMPTY)`
  >- (qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      PairCases_on `cf` >>
      simp[set_constructor_package_target_def, package_constructor_unit_def,
           update_cenv_nonreentrant_def, build_compile_env_unit_def,
           pairTheory.ELIM_UNCURRY] >> strip_tac >> gvs[]) >>
  sg `immutable_section_layout_mods mods ce`
  >- (irule unit_module_locations_immutable_layout >>
      qpat_x_assum `deploy_typing_ok_mods _ _ _ _` mp_tac >>
      simp[deploy_typing_ok_mods_def] >> strip_tac >>
      drule_then assume_tac check_contract_namespaces_ok >>
      fs[contract_namespaces_ok_def, deploy_state_rel_mods_def] >>
      qexistsl_tac [`am`, `exps`, `tx`] >> simp[]) >>
  simp[]
QED
