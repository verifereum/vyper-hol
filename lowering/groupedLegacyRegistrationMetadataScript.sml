(* Static decoder and local-layout facts for a selected legacy package. *)
Theory groupedLegacyRegistrationMetadata
Ancestors
  registrationRejectMetadata externalBodyFrame externalReturnPackage
  defaultEntrySourcePreparation packagedRegistrationProps entryStateRel
  selectedAcceptedSingleton selectedAcceptedDecoder selectedAcceptedInterfaces
  ctorRegisterArgs abiDecoderCoherence immutableRelation
  supportedGetterProps supportedProgram vyperTypeABI e2eDefs
  compileVyper compileEnv moduleLowering vyperInterpreter
  constSubst finite_map list words

Theorem grouped_legacy_registration_metadata:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
    tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
    (FST (classify_functions tops)) /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)) =
    (lbl,ce0,pa,m,pay,nr',key,ut,view,ss,rt) /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  compile_register_positional_args ce0 pa 4 reg = (cf,sa) ==>
  pay = (mut = Payable) /\ nr' = nr /\ key = global_nonreentrant_slot /\
  ut /\ view = (mut = View) /\ rt = (if ret = NoneT then NONE else SOME ret) /\
  ss = subst_consts_stmts (module_consts_env tops []) fbody /\
  pa = build_positional_args ce0 args /\ m = 4 + SUM (MAP tv_abi_size tvs) /\
  m < dimword (:256) /\ ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
  LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce0.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size tv)) args tvs /\
  EVERY (\tv. type_memory_size tv < dimword (:256)) tvs /\
  (!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ce0 with ce_vars := c.ce_vars ==>
    selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
    abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv) /\
  cf with ce_vars := ce0.ce_vars = ce0 /\ local_ptrs_reserved cf sa /\
  (!id ty. MEM (id,ty) args ==>
    (?p sz. FLOOKUP cf.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    cf.ce_var_type id = SOME ty) /\
  (!id loc. FLOOKUP cf.ce_vars id = SOME loc ==> MEM id (MAP FST args)) /\
  cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
  cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
  storage_vars_rel (cf with ce_vars := FEMPTY)
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel (cf with ce_vars := FEMPTY)
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  immutable_section_layout (cf with ce_vars := FEMPTY) tops
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all registration_reject_classified_package_inputs >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  rename1 `LIST_REL _ args (ZIP (MAP SND args,ts))` >>
  `ts = tvs` by fs[] >>
  qpat_x_assum `ts = tvs` SUBST_ALL_TAC >>
  `LENGTH args = LENGTH tvs` by (drule OPT_MMAP_LENGTH >> simp[]) >>
  drule_then assume_tac OPT_MMAP_LIST_REL >>
  suspend "decoder"
QED

Resume grouped_legacy_registration_metadata[decoder]:
  `!i. i < LENGTH args ==>
     abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields (SND (EL i args)) (EL i tvs) /\
     (?loc. FLOOKUP ce0.ce_vars (FST (EL i args)) = SOME loc /\
       var_location_memory_size loc = SOME (type_memory_size (EL i tvs))) /\
     type_memory_size (EL i tvs) < dimword (:256)` by
    (rpt strip_tac >>
     qpat_assum `LIST_REL _ args (ZIP _)`
       (qspec_then `i` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     Cases_on `EL i args` >> simp[EL_ZIP, EL_MAP]) >>
  `LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce0.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size tv)) args tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> _` (qspec_then `n` mp_tac) >>
     Cases_on `EL n args` >> simp[]) >>
  `EVERY (\tv. type_memory_size tv < dimword (:256)) tvs` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     qpat_assum `!i. i < LENGTH args ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  `!c arg tv. MEM (arg,tv) (ZIP (args,tvs)) /\ c = ce0 with ce_vars := c.ce_vars ==>
    selected_slot_accepts c (type_env tops) c.ce_struct_fields (SND arg) tv /\
    abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND arg) tv` by
    (simp[MEM_ZIP] >> rpt strip_tac >> gvs[] >>
     `abi_decoder_coherent c (type_env tops) c.ce_struct_fields (SND (EL n args)) (EL n tvs)` by
       (qpat_assum `c = _` SUBST1_TAC >> simp[ctor_decoder_coherent_vars] >>
        qpat_assum `!i. i < LENGTH args ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
     irule selected_register_one >> irule selected_argument_decoder_accepts >> first_assum ACCEPT_TAC) >>
  suspend "locals"
QED

Resume grouped_legacy_registration_metadata[locals]:
  drule_all target_external_registration_locals >> strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `cf with ce_vars := ce0.ce_vars = ce0` by
    (qpat_assum `cf = _` SUBST1_TAC >> simp[]) >>
  drule_all supported_selected_external_body >> strip_tac >>
  `!id ty. MEM (id,ty) args ==>
    (?p sz. FLOOKUP cf.ce_vars id = SOME (PtrVar (Var p) sz)) /\ cf.ce_var_type id = SOME ty` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (drule_all_then ACCEPT_TAC external_entry_target_param_pointer) >>
     drule_all_then ACCEPT_TAC external_entry_target_param_type) >>
  `!id loc. FLOOKUP cf.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC external_entry_target_declared) >>
  suspend "layout"
QED

Resume grouped_legacy_registration_metadata[layout]:
  drule targeted_external_package_layout >> strip_tac >>
  drule return_package_target_inversion >> strip_tac >>
  drule return_package_metadata >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [combinTheory.K_THM]) >>
  drule_all package_external_fn_vars >> strip_tac >>
  `pay = (mut = Payable) /\ ss = subst_consts_stmts (module_consts_env tops []) fbody` by
    (qpat_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [package_external_fn_def, LET_THM]) >>
  `storage_vars_rel (cf with ce_vars := FEMPTY)
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel (cf with ce_vars := FEMPTY)
    (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule entry_storage_vars_rel_immutable >>
     qpat_assum `cf = _` SUBST1_TAC >>
     qpat_assum `ce0 = _` SUBST1_TAC >>
     simp[initial_evaluation_context_def] >>
     qexistsl_tac [`am`,`tops`,`tx`] >>
     simp[] >> metis_tac[source_typing_ok_vtype_keys_distinct, supported_program_def]) >>
  `ce0.ce_return_pc = NONE` by
    (qpat_assum `ce0 = _` SUBST1_TAC >> simp[]) >>
  `cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\ cf.ce_return_pc = NONE` by
    (qpat_assum `cf = _` SUBST1_TAC >> simp_tac (srw_ss()) [] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `immutable_section_layout (cf with ce_vars := FEMPTY) tops` by
    (qpat_assum `cf = _` SUBST1_TAC >>
     qpat_assum `immutable_section_layout ce0 tops` mp_tac >>
     simp_tac (srw_ss()) [immutable_section_layout_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise grouped_legacy_registration_metadata
