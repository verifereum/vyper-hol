Theory ctorDeployLoweringEntryInputs
Ancestors
  loweringStateRelDefs valueEncodingDefs
 ctorDeployLoweringEntryAggregateInputs ctorDeployLoweringEntryTransport
 ctorDeployLoweringEntrySelection ctorDeployLoweringEntryPrefix
 ctorDeployLoweringEntryRegisterRun abiDecoderTypedContract ctorSourceInputs
 list contractABI vyperABI abiDecoderMembers entryArgPtrs entryDecodeProps
 abiDecoderCoherence abiCallerBuiltinInput compileVyper compileEnv valueEncoding
 vyperState vyperTyping vyperABIRoundtrip supportedProgram supportedDecls
 supportedNames vyperTypeContract vyperInterpreter pair
 vyperTypeContractStaticMaps vyperTypeContractContext
 e2eDeployDefs ctorDeployLoweringDefs ctorDeployDefs ctorDeployLoweringFrame
 e2eEntry venomState venomMemDefs ctorDeployInitcode rich_list

Theorem deploy_ctor_bound_decoder_metadata:
 !tops fargs vals avs scope ce.
 EVERY (supported_value_type tops) (MAP SND fargs) /\
 EVERY (\a. type_memory_bytes ce (SND a) < dimword(:256)) fargs /\
 LENGTH vals = LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     entry.value = EL i vals /\
     evaluate_type (type_env tops) (SND (EL i fargs)) = SOME entry.type /\
     value_has_type entry.type entry.value /\ val_wf entry.type entry.value /\
     type_memory_size entry.type = type_memory_bytes ce (SND (EL i fargs)) /\
     abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     vyper_to_abi (type_env tops) (SND (EL i fargs)) entry.value = SOME (EL i avs)) ==>
 has_types (vyper_to_abi_types (type_env tops) (MAP SND fargs)) avs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce (SND (EL i fargs)) /\
     abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce (type_env tops) (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce.ce_struct_fields ce (SND (EL i fargs)))
       (EL i avs) entry.value)
Proof
 rpt gen_tac >> strip_tac >>
 `!i. i < LENGTH fargs ==>
   has_type (vyper_to_abi_type (type_env tops) (SND (EL i fargs))) (EL i avs) /\
   abi_to_vyper (type_env tops) (SND (EL i fargs)) (EL i avs) = SOME (EL i vals)` by
  (qx_gen_tac `i` >> strip_tac >>
   qpat_x_assum `!i. _ ==> ?entry. _` (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
   irule deploy_supported_value_conversion >>
   gvs[EVERY_EL, EL_MAP] >>
   first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
 conj_tac
 >- (simp[has_types_LIST_REL, vyper_to_abi_types_MAP, LIST_REL_EL_EQN, LENGTH_MAP] >>
     rpt strip_tac >> simp[EL_MAP]) >>
 qx_gen_tac `i` >> strip_tac >>
 qpat_x_assum `!i. _ ==> ?entry. _` (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
 qexists `entry` >> simp[abi_decoder_metadata_def]
QED

Theorem deploy_ctor_target_bound_source_inputs:
 !tops use_trans nkeys mut nr rr fname fargs dflts ret body
 target ce pos_args imm ce0 vals avs scope.
 set_constructor_package_target target
  (package_constructor tops use_trans nkeys
   (mut,nr,rr,fname,fargs,dflts,ret,body)) =
  (ce,pos_args,mut = Payable,nr,nkeys fname,use_trans,body,ret) /\
 ce0 = (ce with ce_imm_alloca := imm) /\
 contract_namespaces_ok T [(NONE,tops)] /\
 EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
 ALL_DISTINCT (MAP FST fargs) /\
 bind_arguments (type_env tops) fargs vals = SOME scope /\
 vyper_to_abi_list (type_env tops) (MAP SND fargs) vals = SOME avs ==>
 pos_args = build_positional_args ce0 fargs /\
 LENGTH vals = LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     entry.value = EL i vals /\
     evaluate_type (type_env tops) (SND (EL i fargs)) = SOME entry.type /\
     value_has_type entry.type entry.value /\ val_wf entry.type entry.value /\
     type_memory_size entry.type = type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     vyper_to_abi (type_env tops) (SND (EL i fargs)) entry.value = SOME (EL i avs)) /\
 (!func initial. local_ptrs_rel func ce0 [scope] initial)
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_target_package_layout >> strip_tac >>
 drule_all deploy_ctor_target_package_memlocs >> strip_tac >>
 drule vyper_to_abi_list_EL >> strip_tac >> fs[LENGTH_MAP] >>
 conj_tac
 >- (qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH fargs` by simp[] >>
     drule_all bind_arguments_lookup_index >> strip_tac >>
     drule_all entryDecodePropsTheory.bind_arguments_word_arg >> strip_tac >>
     `assignable_type (type_env tops) (SND (EL i fargs))` by
       (qpat_x_assum `EVERY (assignable_type _) _` mp_tac >>
        pure_rewrite_tac[EVERY_EL, LENGTH_MAP] >>
        disch_then (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
     rename1 `build_compile_env tops Deploy mut fname fargs ret fbody use_trans` >>
     `abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
       (SND (EL i fargs)) tv` by
       (irule abi_decoder_coherent_layout_transport >>
        qexists `build_compile_env tops Deploy mut fname fargs ret fbody use_trans` >>
        simp[] >> irule abi_caller_coherent >>
        simp[] >> conj_tac >- metis_tac[optionTheory.SOME_11] >>
        qexists `T` >> simp[]) >>
     drule abi_decoder_coherent_header >> strip_tac >>
     qexists `<| assignable := T; type := tv; value := EL i vals; popped := [] |>` >>
     gvs[vyperStateTheory.lookup_scopes_def, abi_decoder_header_def] >>
     conj_tac >- (drule_all bind_arguments_memory_wf >> simp[]) >>
     qpat_x_assum `!i. _ ==> vyper_to_abi _ _ _ = _`
       (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
 rpt gen_tac >>
 qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
 simp[set_constructor_package_target_def, package_constructor_def,
      update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
 simp[local_ptrs_rel_def, local_region_def, cj 3 build_compile_env_vars]
QED

Theorem deploy_ctor_checked_argument_inputs:
 !tops layouts addr art mut nr args body.
 supported_program tops /\
 check_contract T layouts addr [(NONE,tops)] = SOME art /\
 lookup_function NONE "__init__" Deploy tops = SOME (mut,nr,args,[],NoneT,body) ==>
 contract_namespaces_ok T [(NONE,tops)] /\
 ALL_DISTINCT (MAP FST args) /\
 EVERY (assignable_type (type_env tops)) (MAP SND args) /\
 EVERY (supported_value_type tops) (MAP SND args)
Proof
 rpt gen_tac >> strip_tac >>
 `contract_namespaces_ok T [(NONE,tops)]` by
   metis_tac[check_contract_namespaces_ok] >> simp[] >>
 drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
 drule_all supported_program_declaration >>
 simp[supported_function_header_contract, supported_function_argument_def,
      supported_function_header_names_def, supported_declaration_header_def] >>
 strip_tac >>
 qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
 simp[check_contract_def] >> strip_tac >>
 gvs[check_module_def, EVERY_MEM] >>
 qpat_x_assum `!e. MEM e tops ==> check_toplevel_decl _ _ _ _` drule >>
 simp[check_toplevel_decl_def, params_ok_def] >> strip_tac >>
 gvs[deploy_ctor_singleton_type_env, EVERY_MAP, EVERY_MEM, FORALL_PROD,
     supported_function_argument_def, MEM_MAP, EXISTS_PROD] >> metis_tac[]
QED

Theorem deploy_ctor_common_source_witness:
 !tops bc am tx es mut nr body am_c es0 initial.
 deploy_state_rel tops bc am tx es /\
 deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
 constructor_args_encode tops tx initial.vs_data_section ==>
 nr = F /\
 ?args scope avs.
 lookup_function NONE "__init__" Deploy tops = SOME (mut,F,args,[],NoneT,body) /\
 bind_arguments (type_env tops) args tx.args = SOME scope /\
 vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
 initial.vs_data_section =
   enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs)
Proof
 rpt gen_tac >>
 simp[deploy_state_rel_def, deploy_ctor_start_def, constructor_args_encode_def,
      deploy_ctor_singleton_type_env] >> rpt strip_tac >> gvs[] >>
 goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_decoder_inputs:
 !policy tops deploy_bc runtime_bc rp unit dout prog cplan am tx es vs
 body cenv nr key ut imm lbl sa sb sj se sp sf func mut nr' body' am_c es0
 exts ints fb rr fargs ce_pack pos_args imm_opt ce0 initial.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rp,unit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) /\
 deploy_ctor_code tops rp runtime_bc unit
   (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
 classify_functions tops =
   (exts,ints,fb,SOME (mut,nr,rr,"__init__",fargs,[],NoneT,body)) /\
 set_constructor_package_target rp.rpol_target
   (package_constructor tops F (assign_nkeys tops 0)
     (mut,nr,rr,"__init__",fargs,[],NoneT,body)) =
   (ce_pack,pos_args,mut = Payable,nr,key,ut,body,NoneT) /\
 ce0 = (ce_pack with ce_imm_alloca := imm_opt) /\
 initial.vs_data_section = vs.vs_data_section ==>
 nr = F /\ nr' = nr /\ body' = body /\
 pos_args = build_positional_args ce0 fargs /\
 ALL_DISTINCT (MAP FST fargs) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword(:256)) fargs /\
 LENGTH initial.vs_data_section < dimword(:256) /\
 ?scope avs.
 bind_arguments (type_env tops) fargs tx.args = SOME scope /\
 LENGTH avs = LENGTH fargs /\
 initial.vs_data_section =
   enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND fargs))) (ListV avs) /\
 mem_bytes_at 0 (LENGTH initial.vs_data_section) initial.vs_data_section =
   initial.vs_data_section /\
 has_types (vyper_to_abi_types (type_env tops) (MAP SND fargs)) avs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 (type_env tops) (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 local_ptrs_rel func ce0 [scope] initial
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_entry_selection_agrees >> strip_tac >> gvs[] >>
 drule_all deploy_ctor_entry_data_section >> strip_tac >>
 `constructor_args_encode tops tx initial.vs_data_section` by metis_tac[] >>
 drule_all deploy_ctor_common_source_witness >> strip_tac >>
 qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac classify_functions_ctor_lookup >>
 simp[] >> strip_tac >> gvs[] >>
 `supported_program tops /\ ?art.
   check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
   fs[deploy_source_ok_def, deploy_typing_ok_def] >>
 drule_all deploy_ctor_checked_argument_inputs >> strip_tac >>
 `ut = F /\ key = assign_nkeys tops 0 "__init__"` by
   fs[set_constructor_package_target_def, package_constructor_def] >>
 fs[] >>
 drule deploy_ctor_target_package_layout >>
 disch_then (qspecl_then [`imm_opt`, `ce_pack with ce_imm_alloca := imm_opt`] mp_tac) >>
 simp[] >> strip_tac >>
 drule_all deploy_ctor_allocation_bounds >> strip_tac >>
 `ce_pack.ce_struct_fields = cenv.ce_struct_fields` by
   (drule deploy_ctor_static_tables >> strip_tac >>
    simp[build_compile_env_ce_struct_fields]) >>
 `EVERY (\a. type_memory_bytes (ce_pack with ce_imm_alloca := imm_opt) (SND a)
    < dimword(:256)) args` by
   (irule deploy_ctor_argument_bounds_transport >> qexists `cenv` >> simp[]) >>
 drule deploy_ctor_target_bound_source_inputs >>
 disch_then (qspecl_then [`imm_opt`, `ce_pack with ce_imm_alloca := imm_opt`] mp_tac) >>
 simp_tac bool_ss [] >> disch_then drule_all >> strip_tac >>
 drule_all deploy_ctor_bound_decoder_metadata >> strip_tac >>
 drule_all deploy_ctor_entry_data_size >> strip_tac >>
 gvs[mem_bytes_at_def, TAKE_LENGTH_APPEND] >> qexists `avs` >> simp[]
QED
