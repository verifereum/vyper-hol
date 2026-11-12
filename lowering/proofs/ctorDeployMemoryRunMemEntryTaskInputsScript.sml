Theory ctorDeployMemoryRunMemEntryTaskInputs
Ancestors
  ctorDeployMemoryRunMemEntryTaskRegistration ctorDeployInitcode
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs compileVyper
  vyperInterpreter vyperTypeContractStaticMaps list words

Theorem ctor_task_encoded_source:
  SND (SND (SND (classify_functions tops))) =
    SOME (fmut,fnr,rr,fname,fargs,dflts,ret,fbody) /\
  fname = "__init__" /\ constructor_args_encode tops tx encoded ==>
  fnr = F /\ dflts = [] /\ ret = NoneT /\
  ?scope avs.
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    vyper_to_abi_list (type_env tops) (MAP SND fargs) tx.args = SOME avs /\
    encoded = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND fargs)))
      (ListV avs)
Proof
  strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >> simp[] >> strip_tac >>
  gvs[constructor_args_encode_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

Theorem ctor_task_start_source:
  SND (SND (SND (classify_functions tops))) =
    SOME (fmut,fnr,rr,fname,fargs,dflts,ret,fbody) /\
  fname = "__init__" /\ tx.function_name = "__init__" /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  fmut = mut /\ fnr = nr /\ dflts = [] /\ ret = NoneT /\ fbody = stmts
Proof
  strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >> simp[] >> strip_tac >>
  gvs[deploy_ctor_start_def]
QED

Theorem ctor_task_encoded_size:
  deploy_phases policy tops (deploy_bc,runtime_bc) arts /\
  deploy_source_ok tops am tx /\ constructor_args_encode tops tx encoded ==>
  LENGTH encoded < dimword (:256)
Proof
  strip_tac >> drule_all constructor_args_size_bounded >>
  simp[dimword_def]
QED

Theorem ctor_task_data_section:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  ?encoded. constructor_args_encode tops tx encoded /\
    vs.vs_data_section = encoded
Proof
  strip_tac >>
  `vs.vs_data_section =
    (deploy_entry_state prog cplan tops es).vs_data_section` by
    (gvs[o1PassContractTheory.gas_variant_def] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_data_section`) >>
     simp[]) >>
  gvs[deploy_state_rel_def, deploy_phases_def, deploy_entry_state_def,
      e2eEntryTheory.entry_venom_state_def] >>
  metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem ctor_task_checked_params:
  check_contract in_deploy layouts (addr:address) mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  vyperInterpreter$lookup_function NONE fname Deploy ts =
    SOME (mut,nr,args,dflts,ret,stmts) ==>
  params_ok (type_env_all_modules mods) args
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  simp[vyperTypeContractTheory.params_ok_def] >>
  gvs[vyperTypeContractTheory.check_contract_def, EVERY_MEM] >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >>
  simp[vyperTypeContractTheory.check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!e. MEM e ts ==> check_toplevel_decl _ _ _ _` drule >>
  simp[vyperTypeContractTheory.check_toplevel_decl_def,
       vyperTypeContractTheory.params_ok_def, EVERY_MEM]
QED

Theorem ctor_task_lowered_source:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops =
    (exts,ints,fb,SOME (mut,nr,rr,fname,fargs,dflts,ret,stmts)) /\
  supported_program tops ==>
  fname = "__init__" /\
  fn_allocs_ok tops (mut,nr,rr,fname,fargs,dflts,ret,stmts) /\
  EVERY (supported_value_type tops) (MAP SND fargs)
Proof
  strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >>
  simp[ctor_named_init_def] >> strip_tac >>
  drule_all ctorDeployMemoryRunMemEntrySupportTheory.ctor_classified_constructor_supported >>
  strip_tac >> simp[] >>
  irule lower_vyper_deploy_unit_allocs_ok >> simp[] >> metis_tac[]
QED

Theorem ctor_task_checked_namespaces:
  deploy_source_ok tops am tx ==>
  contract_namespaces_ok T [((NONE:num option),tops)] /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  simp[deploy_source_ok_def, deploy_typing_ok_def] >> strip_tac >>
  `contract_namespaces_ok T [((NONE:num option),tops)]` by
    gvs[vyperTypeContractTheory.check_contract_def] >>
  simp[] >> irule contract_namespaces_ok_module_type_def_keys >>
  qexists_tac `[(NONE,tops)]` >>
  gvs[vyperTypeContractTheory.check_contract_def]
QED

Theorem ctor_task_source_params:
  deploy_source_ok tops am tx /\
  vyperInterpreter$lookup_function NONE fname Deploy tops =
    SOME (mut,nr,args,dflts,ret,stmts) ==>
  ALL_DISTINCT (MAP FST args) /\
  EVERY (assignable_type (type_env tops)) (MAP SND args)
Proof
  strip_tac >>
  `params_ok (type_env_all_modules [(NONE,tops)]) args` by
    (irule ctor_task_checked_params >>
     gvs[deploy_source_ok_def, deploy_typing_ok_def] >>
     conj_tac >- (qexistsl [`tx.target`, `deploy_art`, `T`, `am.layouts`] >> simp[]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[vyperTypeContractTheory.params_ok_def,
      e2eProducersTheory.type_env_all_modules_single, EVERY_MAP,
      combinTheory.o_DEF, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >>
  pairarg_tac >> simp[]
QED

Theorem ctor_task_aligned_inputs:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops =
    (exts,ints,fb,SOME (fmut,fnr,rr,fname,fargs,dflts,ret,fbody)) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  fname = "__init__" /\ fmut = mut /\ fnr = nr /\ nr = F /\
  dflts = [] /\ ret = NoneT /\ fbody = stmts /\
  fn_allocs_ok tops (fmut,fnr,rr,fname,fargs,dflts,ret,fbody) /\
  EVERY (supported_value_type tops) (MAP SND fargs) /\
  ALL_DISTINCT (MAP FST fargs) /\
  EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
  ?encoded scope avs.
    constructor_args_encode tops tx encoded /\
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    vyper_to_abi_list (type_env tops) (MAP SND fargs) tx.args = SOME avs /\
    encoded = enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND fargs)))
      (ListV avs)
Proof
  strip_tac >>
  `supported_program tops` by gvs[deploy_source_ok_def] >>
  drule_all ctor_task_lowered_source >> strip_tac >>
  `tx.function_name = "__init__" /\
   ?encoded. constructor_args_encode tops tx encoded` by
    (gvs[deploy_state_rel_def] >> metis_tac[]) >>
  `SND (SND (SND (classify_functions tops))) =
    SOME (fmut,fnr,rr,fname,fargs,dflts,ret,fbody)` by simp[] >>
  drule_all ctor_task_start_source >> strip_tac >>
  drule_all ctor_task_encoded_source >> strip_tac >>
  `vyperInterpreter$lookup_function NONE fname Deploy tops =
    SOME (fmut,fnr,fargs,dflts,ret,fbody)` by
    (qspecl_then [`tops`, `NONE`, `fname`] mp_tac
      classify_functions_ctor_lookup >> simp[]) >>
  drule_all ctor_task_source_params >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem ctor_task_target_layout:
  build_positional_args (ce with ce_target := target) args =
    build_positional_args ce args /\
  type_memory_bytes (ce with ce_target := target) = type_memory_bytes ce /\
  type_to_abi_dec_info sf (ce with ce_target := target) ty =
    type_to_abi_dec_info sf ce ty /\
  (abi_decoder_coherent (ce with ce_target := target) env sf ty tv <=>
    abi_decoder_coherent ce env sf ty tv)
Proof
  rpt conj_tac
  >- (irule build_positional_args_layout_cong >> simp[])
  >- (irule compileEnvTheory.type_memory_bytes_frame >> simp[])
  >- (irule exprLoweringTheory.type_to_abi_dec_info_layout_cong >> simp[]) >>
  irule abiDecoderCoherenceTheory.abi_decoder_coherent_layout_cong >> simp[]
QED

Theorem ctor_task_target_metadata:
  abi_decoder_metadata (ce with ce_target := target) env ty tv di av v <=>
  abi_decoder_metadata ce env ty tv di av v
Proof
  simp[abiDecoderTypedContractTheory.abi_decoder_metadata_def,
    ctor_task_target_layout]
QED

Theorem ctor_task_encoding_unique:
  constructor_args_encode tops tx xs /\
  constructor_args_encode tops tx ys ==> xs = ys
Proof
  simp[constructor_args_encode_def] >> rpt strip_tac >> gvs[]
QED

Theorem ctor_task_actual_encoded_inputs:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops =
    (exts,ints,fb,SOME (fmut,fnr,rr,fname,fargs,dflts,ret,fbody)) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  fname = "__init__" /\ fmut = mut /\ fnr = nr /\ nr = F /\
  dflts = [] /\ ret = NoneT /\ fbody = stmts /\
  fn_allocs_ok tops (fmut,fnr,rr,fname,fargs,dflts,ret,fbody) /\
  EVERY (supported_value_type tops) (MAP SND fargs) /\
  ALL_DISTINCT (MAP FST fargs) /\
  EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
  ?scope avs.
    bind_arguments (type_env tops) fargs tx.args = SOME scope /\
    vyper_to_abi_list (type_env tops) (MAP SND fargs) tx.args = SOME avs /\
    constructor_args_encode tops tx vs.vs_data_section /\
    vs.vs_data_section =
      enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND fargs)))
        (ListV avs) /\
    LENGTH vs.vs_data_section < dimword (:256)
Proof
  strip_tac >>
  drule_all ctor_task_aligned_inputs >> strip_tac >>
  drule_all ctor_task_data_section >> strip_tac >>
  `!xs ys. constructor_args_encode tops tx xs /\
            constructor_args_encode tops tx ys ==> xs = ys` by
    metis_tac[ctor_task_encoding_unique] >>
  `vs.vs_data_section = encoded` by metis_tac[] >>
  drule_all ctor_task_encoded_size >> strip_tac >>
  gvs[] >> metis_tac[]
QED
