Theory entryExternalPackageCoherence
Ancestors
  compileVyper compileEnv abiCallerBuiltinInput abiDecoderCoherence
  vyperContext vyperTypeSystem vyperTypeContract list

Theorem external_package_layout:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  specs = build_positional_args ce args /\
  ce.ce_struct_fields =
    (build_compile_env tops External mut fname args ret fbody use_trans).ce_struct_fields /\
  ce.ce_flag_n_members =
    (build_compile_env tops External mut fname args ret fbody use_trans).ce_flag_n_members
Proof
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_ret_abi_def] >> rpt strip_tac >> gvs[] >>
  irule build_positional_args_layout_cong >> simp[]
QED

Theorem external_package_decoder_coherent:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv
Proof
  strip_tac >> drule external_package_layout >> strip_tac >>
  irule abi_decoder_coherent_layout_transport >>
  qexists `build_compile_env tops External mut fname args ret fbody use_trans` >>
  simp[] >> irule abi_caller_coherent >> simp[] >>
  qexists `in_deploy` >> simp[]
QED

Theorem external_package_layout_sizes[local]:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (type_env tops) ty)
Proof
  strip_tac >> drule_all external_package_decoder_coherent >> strip_tac >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]
QED
