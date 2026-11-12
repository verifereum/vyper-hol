Theory entrySelectedPackageCoherence
Ancestors
  entryExternalPackageCoherence entryParameterAdmissibility
  abiDecoderCoherence compileVyper compileEnv e2eDefs
  vyperTypeContractStaticMaps vyperTypeSystem vyperTypeContract
  vyperContext vyperInterpreter vyperABI contractABI list

Theorem source_runtime_namespaces[local]:
  source_typing_ok tops am tx ==>
  contract_namespaces_ok F [((NONE:num option),tops)]
Proof
  strip_tac >> gvs[source_typing_ok_def] >>
  drule check_contract_runtime_namespaces >> simp[]
QED

Theorem selected_external_package_decoder_coherent:
  source_typing_ok tops am tx /\ supported_program tops /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (name,ty) args /\ evaluate_type (type_env tops) ty = SOME tv /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv
Proof
  strip_tac >> drule_all selected_external_parameter_assignable >> strip_tac >>
  drule source_runtime_namespaces >> strip_tac >>
  irule external_package_decoder_coherent >>
  simp[] >> conj_tac
  >- (goal_assum (drule_at Any)) >>
  qexists `F` >> simp[]
QED

Theorem selected_external_package_layout_sizes:
  source_typing_ok tops am tx /\ supported_program tops /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (name,ty) args /\ evaluate_type (type_env tops) ty = SOME tv /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (type_env tops) ty)
Proof
  strip_tac >> drule_all selected_external_package_decoder_coherent >> strip_tac >>
  drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]
QED
