(* Pure metadata transport from a runtime package through any registration prefix. *)
Theory entryReachBodyPackageAlignment
Ancestors
  returnMetadataPtr calldataRegistration entryReachBodySourceMemberEntry
  e2eDefs supportedProgram supportedDecls vyperABIRoundtrip
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeContract
  entryReachBodySourceSupport entryReachBodyCallInputs ctorSourceInputs
  abiCallerBuiltinInput abiDecoderCoherence entryStateRel entryArgPtrs
  compileVyper compileEnv structFieldsProps entryDecodeStaticProps exprLowering list finite_map
val _ = Parse.hide "body";

Theorem entry_runtime_package_layout:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,ce,pos,cds,pay,nr',key,ut,view,body',rt) ==>
  pos = build_positional_args ce args /\
  ce.ce_struct_fields =
    (build_compile_env tops External mut name args ret body use_trans).ce_struct_fields /\
  ce.ce_flag_n_members =
    (build_compile_env tops External mut name args ret body use_trans).ce_flag_n_members /\
  ce.ce_vars =
    (build_compile_env tops External mut name args ret body use_trans).ce_vars /\
  ce.ce_is_ctor = F
Proof
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  (simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
   strip_tac >> gvs[] >> rpt conj_tac
   >~ [`build_positional_args _ _ = build_positional_args _ _`]
   >- (irule build_positional_args_layout_cong >> simp[]) >>
   simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]))
QED

Theorem entry_registration_prefix_layout:
  compile_register_positional_args ce args off st = (next,last) ==>
  next.ce_struct_fields = ce.ce_struct_fields /\
  next.ce_flag_n_members = ce.ce_flag_n_members /\
  next.ce_is_ctor = ce.ce_is_ctor /\
  build_positional_args next suffix = build_positional_args ce suffix
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `next = _` SUBST1_TAC >> simp[] >>
  irule build_positional_args_layout_cong >> simp[]
QED

Theorem entry_runtime_prefix_coherent:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,ce,pos,cds,pay,nr',key,ut,view,body',rt) /\
  compile_register_positional_args ce prefix off st = (next,last) /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent next (type_env tops) next.ce_struct_fields ty tv
Proof
  strip_tac >> drule entry_runtime_package_layout >> strip_tac >>
  drule entry_registration_prefix_layout >> strip_tac >>
  irule abi_decoder_coherent_layout_transport >>
  qexists_tac `build_compile_env tops External mut name args ret body use_trans` >>
  simp[] >> irule abi_caller_coherent >> metis_tac[]
QED

Theorem entry_prefix_source_metadata:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  entry_abi_support env ty /\ value_has_type tv value /\
  vyper_to_abi env ty value = SOME av ==>
  entry_source_metadata ce env ce.ce_struct_fields ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av value
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, entry_source_metadata_def]
QED

Theorem entry_prefix_descriptor:
  compile_register_positional_args ce prefix off st = (next,last) /\
  abi_decoder_coherent next env next.ce_struct_fields ty tv /\
  build_positional_arg ce (name,ty) = (n,prim,dyn,sz,info) ==>
  n = name /\ prim = is_word_type ty /\
  info = type_to_abi_dec_info next.ce_struct_fields next ty /\
  (dyn /\ ~prim <=> is_dynamic (vyper_to_abi_type env ty)) /\
  sz = abi_member_head_size (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule entry_registration_prefix_layout >> strip_tac >>
  `build_positional_arg next (name,ty) = build_positional_arg ce (name,ty)` by
    (first_x_assum (qspec_then `[(name,ty)]` mp_tac) >>
     simp_tac (srw_ss()) [build_positional_args_def]) >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  gvs[build_positional_arg_def] >>
  metis_tac[word_type_dec_sizes]
QED

Theorem entry_selected_parameter_types:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  contract_namespaces_ok F [(NONE,tops)] /\
  EVERY (assignable_type (type_env tops)) (MAP SND args) /\
  EVERY (supported_place_type tops) (MAP SND args)
Proof
  strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw tx.function_name args [] ret fbody) tops` by
    (irule lookup_function_external_decl >> simp[] >> qexists_tac `tops` >>
     gvs[supported_program_def, supported_declaration_headers_def]) >>
  `EVERY (supported_place_type tops) (MAP SND args)` by
    (gvs[supported_program_def, supported_declaration_headers_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e tops ==> supported_declaration_header tops e` drule >>
     simp[supported_declaration_header_def, supported_function_argument_def,
       EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD] >>
     strip_tac >> rpt strip_tac >> PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  gvs[source_typing_ok_def] >>
  `contract_namespaces_ok F [(NONE,tops)]` by metis_tac[check_contract_namespaces_ok] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (drule check_contract_main_module_allocated >> simp[]) >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     External mut F args [] ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     qexistsl_tac [`tx.function_name`, `raw`] >> simp[]) >>
  gvs[check_function_body_def, params_ok_def, EVERY_MAP, EVERY_MEM,
    pairTheory.FORALL_PROD, combinTheory.o_DEF,
    vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def] >>
  metis_tac[]
QED

Theorem entry_runtime_package_memlocs:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,ce,pos,cds,pay,nr',key,ut,view,body',rt) /\
  ALL_DISTINCT (MAP FST args) ==>
  EVERY (\a. ?p. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc p (type_memory_bytes ce (SND a)))) args
Proof
  strip_tac >> drule entry_runtime_package_layout >> strip_tac >>
  `ce.ce_struct_fields = make_struct_fields_map tops` by
    simp[build_compile_env_ce_struct_fields] >>
  `ce.ce_vars = FST (allocate_args
     (get_struct_fields (make_struct_fields_map tops)) args 0 FEMPTY)` by
    (simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule_then (qspecl_then [`get_struct_fields (make_struct_fields_map tops)`,
    `0`, `FEMPTY`] strip_assume_tac) allocate_args_lookup >>
  gvs[EVERY_MEM, GSYM type_mem_bytes_type_memory_bytes]
QED

Theorem entry_unprocessed_parameter_size:
  compile_register_positional_args ce prefix off st = (next,last) /\
  ~MEM name (MAP FST prefix) /\
  FLOOKUP ce.ce_vars name = SOME (MemLoc p (type_memory_bytes ce ty)) /\
  abi_decoder_coherent next env next.ce_struct_fields ty tv ==>
  FLOOKUP next.ce_vars name = SOME (MemLoc p (type_memory_size tv)) /\
  var_location_memory_size (MemLoc p (type_memory_size tv)) = SOME (type_memory_size tv)
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `type_memory_bytes next ty = type_memory_bytes ce ty` by
    (irule type_memory_bytes_struct_fields >>
     qpat_x_assum `next = _` SUBST1_TAC >> simp[]) >>
  simp[moduleLoweringTheory.var_location_memory_size_def] >> metis_tac[]
QED

(* The actual selected call supplies the pure semantic premises of the
   resource singleton, independently of its code and allocation premises. *)
Theorem entry_selected_source_values:
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope ==>
  ?avs. vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
    LENGTH avs = LENGTH args /\ LENGTH tx.args = LENGTH args /\
    EVERY (entry_abi_support (type_env tops)) (MAP SND args) /\
    LIST_REL (\ty v. ?tv. evaluate_type (type_env tops) ty = SOME tv /\
      value_has_type tv v) (MAP SND args) tx.args /\
    (!i. i < LENGTH args ==>
      ?tv. evaluate_type (type_env tops) (SND (EL i args)) = SOME tv /\
        value_has_type tv (EL i tx.args) /\
        vyper_to_abi (type_env tops) (SND (EL i args)) (EL i tx.args) = SOME (EL i avs))
Proof
  strip_tac >> drule_all entry_call_canonical_tuple >> strip_tac >>
  drule_all entry_selected_parameter_types >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  qexists_tac `avs` >> simp[] >>
  `!i. i < LENGTH args ==> ?tv.
    evaluate_type (type_env tops) (SND (EL i args)) = SOME tv /\
    value_has_type tv (EL i tx.args)` by
    metis_tac[entryDecodePropsTheory.bind_arguments_word_arg] >>
  conj_tac
  >- (simp[EVERY_EL, LENGTH_MAP, EL_MAP] >> rpt strip_tac >>
      irule entry_supported_place_evaluated >>
      fs[EVERY_EL, EL_MAP] >> metis_tac[]) >>
  conj_tac
  >- (simp[LIST_REL_EL_EQN, LENGTH_MAP, EL_MAP] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH tx.args ==> _` (qspec_then `i` mp_tac) >>
  simp[EL_MAP] >> metis_tac[]
QED
