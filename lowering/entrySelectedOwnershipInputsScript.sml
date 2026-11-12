(* Natural capacities and source-selected owned registration inputs. *)
Theory entrySelectedOwnershipInputs
Ancestors
  entrySelectedDescriptorValues entrySelectedLocationMetadata
  entryCapacitySourceProbe entryRuntimeSlice entryExternalPackageCoherence
  supportedProgram compileVyper compileEnv e2eDefs list pair

Theorem selected_package_allocation_layout[local]:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  ce.ce_struct_fields = make_struct_fields_map tops /\
  ce.ce_event_info = build_event_info (type_env tops) tops (K NONE)
Proof
  simp[package_external_fn_def, set_external_package_target_def,
    update_cenv_nonreentrant_def] >>
  Cases_on `ret = NoneT` >> gvs[update_cenv_ret_abi_def] >>
  rpt strip_tac >> gvs[] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> simp[])
QED

Theorem selected_package_parameter_nonwrap[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\ supported_program tops /\
  valid_vyper_call tops tx calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) /\
  MEM (name,ty) args ==>
  type_memory_bytes ce ty < dimword (:256)
Proof
  strip_tac >> drule selected_package_allocation_layout >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supportedDeclsTheory.supported_declaration_headers_def] >>
  `tx.function_name <> "__default__"` by gvs[valid_vyper_call_def] >>
  drule_all supported_external_lookup_classified >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  irule lowered_external_parameter_nonwrap >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem evaluated_values_capacity[local]:
  !args values.
  LIST_REL (\(name,ty) (ty',tv,v,at,av).
    ty' = ty /\ evaluate_type env ty = SOME tv) args values /\
  (!name ty. MEM (name,ty) args ==> type_memory_bytes ce ty < dimword (:256)) ==>
  EVERY (\(ty,tv,v,at,av). type_memory_bytes ce ty < dimword (:256)) values
Proof
  Induct >> Cases_on `values` >> simp[] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem selected_external_owned_descriptor_values:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,ce,specs,min_cds,payable,nr',nk,ut,iv,stmts,rt) ==>
  ?values.
    LIST_REL (\(name,ty) (ty',tv,v,at,av).
      ty' = ty /\ evaluate_type (type_env tops) ty = SOME tv) args values /\
    MAP (\(ty,tv,v,at,av). v) values = tx.args /\
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
      sz = abi_embedded_static_size ce.ce_struct_fields ty /\ sz = abi_member_head_size at /\
      type_memory_bytes ce ty = type_memory_size tv /\
      (prim ==> ?c. info = DecPrimWord c) /\ (dyn /\ ~prim <=> is_dynamic at) /\
      value_has_type tv v /\ vyper_to_abi (type_env tops) ty v = SOME av /\
      at = vyper_to_abi_type (type_env tops) ty /\
      type_memory_size tv < dimword (:256)) specs values /\
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) specs values /\
    ALL_DISTINCT (MAP (\(name,prim,dyn,sz,info). name) specs) /\
    has_types (MAP (\(ty,tv,v,at,av). at) values)
      (MAP (\(ty,tv,v,at,av). av) values) /\
    vs.vs_call_ctx.cc_calldata =
      function_selector tx.function_name (MAP (\(ty,tv,v,at,av). at) values) ++
      enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
        (ListV (MAP (\(ty,tv,v,at,av). av) values))
Proof
  strip_tac >> drule_all selected_external_descriptor_values >> strip_tac >>
  drule_all selected_external_evaluated_value_locations >> strip_tac >>
  drule_all selected_external_package_distinct_names >> strip_tac >>
  `!name ty. MEM (name,ty) args ==> type_memory_bytes ce ty < dimword (:256)` by
    (rpt strip_tac >> irule selected_package_parameter_nonwrap >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all evaluated_values_capacity >> strip_tac >>
  qexists_tac `values` >> simp[] >>
  qpat_x_assum `LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent _ _ _ _ _ /\ _) _ _`
    mp_tac >>
  qpat_x_assum `EVERY _ values` mp_tac >>
  simp[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  first_x_assum (qspec_then `n` mp_tac) >>
  qabbrev_tac `spec = EL n specs` >> qabbrev_tac `value = EL n values` >>
  PairCases_on `spec` >> PairCases_on `value` >> simp[] >> metis_tac[]
QED
