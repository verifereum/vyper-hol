Theory entrySelectedLocationMetadata
Ancestors
  entrySelectedDescriptorValues entryParameterAdmissibility entryExternalPackageCoherence
  entryPackageDescriptorFacts entryStateRel compileVyper compileEnv moduleLowering
  vyperTypeSystem vyperTypeContract vyperTyping list rich_list pair finite_map

Theorem selected_external_package_distinct_names:
  supported_program tops /\ source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  ALL_DISTINCT (MAP (\(name,prim,dyn,sz,info). name) specs)
Proof
  strip_tac >> drule_all selected_external_params_ok >>
  simp[params_ok_def] >> strip_tac >>
  drule external_package_layout >> strip_tac >>
  `MAP (\(name,prim,dyn,sz,info). name) (build_positional_args ce args) =
    MAP FST args` by
    (simp[build_positional_args_def, MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[FORALL_PROD, build_positional_arg_def]) >>
  simp[]
QED

Theorem target_external_package_arg_locations[local]:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  ALL_DISTINCT (MAP FST args) ==>
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args
Proof
  Cases_on `package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,args,dflts,ret,fbody)` >>
  PairCases_on `r` >>
  simp[set_external_package_target_def] >> strip_tac >> gvs[] >>
  `type_memory_bytes (r0 with ce_target := target) = type_memory_bytes r0` by
    (irule type_memory_bytes_frame >> simp[]) >>
  drule_all package_external_fn_vars >> simp[]
QED

Theorem package_descriptor_locations[local]:
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) args /\
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ type_memory_bytes ce ty = type_memory_size tv) args values ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv))
    (build_positional_args ce args) values
Proof
  qid_spec_tac `values` >> Induct_on `args` >> Cases_on `values` >>
  simp[build_positional_args_def] >> gen_tac >>
  PairCases_on `h` >> PairCases_on `h'` >>
  simp[build_positional_arg_def, GSYM build_positional_args_def] >> rpt strip_tac
  >- (goal_assum (drule_at Any) >> simp[var_location_memory_size_def]) >>
  first_x_assum irule >> simp[]
QED

Theorem selected_external_package_value_locations[local]:
  supported_program tops /\ source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ type_memory_bytes ce ty = type_memory_size tv) args values ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) specs values
Proof
  strip_tac >> drule_all selected_external_params_ok >>
  simp[params_ok_def] >> strip_tac >>
  drule_all target_external_package_arg_locations >> strip_tac >>
  drule external_package_layout >> strip_tac >> gvs[] >>
  irule package_descriptor_locations >> simp[]
QED

Theorem evaluated_source_memory_alignment[local]:
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ evaluate_type env ty = SOME tv) args values /\
  (!name ty tv. MEM (name,ty) args /\ evaluate_type env ty = SOME tv ==>
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv) ==>
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ type_memory_bytes ce ty = type_memory_size tv) args values
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `MEM (FST (EL n args),SND (EL n args)) args` by
    (simp[] >> irule EL_MEM >> simp[]) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  qabbrev_tac `arg = EL n args` >> qabbrev_tac `value = EL n values` >>
  PairCases_on `arg` >> PairCases_on `value` >> simp[] >> strip_tac >> gvs[] >>
  `abi_decoder_coherent ce env ce.ce_struct_fields arg1 value1` by metis_tac[] >>
  drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
  simp[abiDecoderCoherenceTheory.abi_decoder_header_def]
QED

Theorem selected_external_evaluated_value_locations:
  supported_program tops /\ source_typing_ok tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ evaluate_type (type_env tops) ty = SOME tv) args values ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) specs values
Proof
  strip_tac >> irule selected_external_package_value_locations >>
  goal_assum (drule_at Any) >> simp[] >> qexists `am` >> simp[] >>
  irule evaluated_source_memory_alignment >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  irule entrySelectedPackageCoherenceTheory.selected_external_package_decoder_coherent >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
