Theory linkedExternalEntryExprInvariant
Ancestors
  exprSimHypsDefs bodyInvSplit bodyInvCodeProps bodyCallSupport
  linkedEntryBodyTables linkedFlagCount linkedStructFields linkedStructMemorySize
  linkedStorageMetadataProps linkedStorageLocationOrigin placeTypingProps
  structFieldsProps abiCallerStructSize
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeConstantFold
  vyperTypeInvariants vyperContext vyperAST loweringStateRelDefs compileUnit compileEnv
  finite_map list pair alist words arithmetic

Theorem linked_external_entry_expr_sim_inv_mods:
  contract_inv mods exps ctx registered_env cx /\
  module_body_inv mods src tops registered_env cx /\
  ~cx.in_deploy /\
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  get_tenv cx = type_env_all_modules mods /\
  entry_types.current_src = src /\
  entry_types.fn_sigs = art.cta_fn_sigs /\
  entry_types.toplevel_vtypes = art.cta_toplevel_vtypes /\
  entry_types.bare_globals = art.cta_bare_globals /\
  entry_types.bare_global_assignable = FEMPTY /\
  imm_len_mods mods < 24576 /\
  env_consistent entry_types cx es /\ state_well_typed es /\
  accounts_well_typed es.accounts /\ context_well_typed cx /\
  functions_well_typed cx /\ outcomes_accounts_typed es.outcomes /\
  IS_SOME es.outcomes /\ popped_keys_indexed es.scopes /\
  (!id ty. FLOOKUP entry_types.var_types id = SOME ty ==>
     ?p sz. FLOOKUP registered_env.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP entry_types.var_types id = SOME ty ==>
     registered_env.ce_var_type id = SOME ty) ==>
  expr_sim_inv_mods mods registered_env cx entry_types es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `registered_env.ce_struct_fields = make_struct_fields_map_mods mods` by
    drule_then ACCEPT_TAC contract_inv_struct_fields >>
  `env_context_consistent entry_types cx` by
    (qpat_assum `env_consistent entry_types cx es`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [env_consistent_def])) >>
  `linked_fn_sigs_declared mods cx entry_types.fn_sigs` by
    (qpat_assum `entry_types.fn_sigs = art.cta_fn_sigs` SUBST1_TAC >>
     `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art` by
       (qpat_assum `~cx.in_deploy` (fn runtime =>
          qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
            (fn checked => simp[NoAsms, runtime, checked]))) >>
     drule_then ACCEPT_TAC check_contract_linked_fn_sigs_declared) >>
  `contract_namespaces_ok F mods` by
    (qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
       (ACCEPT_TAC o MATCH_MP check_contract_runtime_namespaces)) >>
  `!fid sig. FLOOKUP entry_types.fn_sigs fid = SOME sig ==>
      registered_env.ce_func_return_type (nsid_to_string fid) = sig.ret_ty` by
    (rpt strip_tac >> PairCases_on `fid` >>
     `FLOOKUP (build_contract_type_artifact F mods).cta_fn_sigs (fid0,fid1) = SOME sig` by
       (qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
          (strip_assume_tac o MATCH_MP check_contract_artifact_fields) >>
        qpat_assum `FLOOKUP entry_types.fn_sigs (fid0,fid1) = SOME sig` mp_tac >>
        qpat_assum `entry_types.fn_sigs = art.cta_fn_sigs` (fn entry =>
          qpat_assum `art.cta_fn_sigs = _` (fn checked =>
            simp[NoAsms, entry, checked, FLOOKUP_DRESTRICT_SOME]))) >>
     drule_all_then strip_assume_tac build_contract_type_artifact_fn_sigs_declared_sound >>
     `vis <> External` by
       (qpat_assum `include_fn_sig F vis` mp_tac >>
        Cases_on `vis` >> simp[NoAsms, include_fn_sig_def]) >>
     drule_all_then ACCEPT_TAC linked_entry_declared_return_type) >>
  `!sid fid ts ls mid i.
      get_module_code cx sid = SOME ts /\ lookup_flag fid ts = SOME ls /\
      INDEX_OF mid ls = SOME i ==>
      registered_env.ce_flag_member_id (nsid_to_string (sid,fid)) mid = i` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC linked_entry_flag_member_id) >>
  `!nsid m. FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m) ==>
      registered_env.ce_flag_n_members (nsid_to_string nsid) = m` by
    (rpt gen_tac >>
     qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
     qpat_assum `contract_inv mods exps ctx registered_env cx`
       (strip_assume_tac o REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
     qpat_assum `registered_env.ce_flag_n_members = _` SUBST1_TAC >> strip_tac >>
     drule_all_then ACCEPT_TAC linked_flag_member_count) >>
  `!fname tys. registered_env.ce_method_id fname tys =
      w2n (calldata_method_id
        (function_selector fname (vyper_to_abi_types (get_tenv cx) tys)))` by
    (qpat_assum `contract_inv mods exps ctx registered_env cx`
       (strip_assume_tac o REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
     qpat_assum `registered_env.ce_method_id = _` SUBST1_TAC >>
     qpat_assum `get_tenv cx = _` (fn tenv => simp[NoAsms, tenv])) >>
  `sfields_tenv_consistent registered_env.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `get_tenv cx = _` SUBST1_TAC >>
     qpat_assum `registered_env.ce_struct_fields = _` SUBST1_TAC >>
     drule_then ACCEPT_TAC make_struct_fields_map_mods_consistent) >>
  `!field_key fields.
      FLOOKUP registered_env.ce_struct_fields field_key = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
          sz = type_memory_size tv) fields` by
    (qx_genl_tac [`field_key`,`fields`] >> strip_tac >>
     qpat_assum `sfields_tenv_consistent registered_env.ce_struct_fields (get_tenv cx)`
       (strip_assume_tac o REWRITE_RULE [sfields_tenv_consistent_def]) >>
     qpat_assum `!name fields. FLOOKUP registered_env.ce_struct_fields name = SOME fields ==> _`
       (drule_then (qx_choosel_then [`nsid`,`struct_args`] strip_assume_tac)) >>
     `FLOOKUP (type_env_all_modules mods) nsid = SOME (StructArgs struct_args)` by
       (qpat_assum `get_tenv cx = _` (fn tenv =>
          qpat_assum `FLOOKUP (get_tenv cx) nsid = _` (ACCEPT_TAC o REWRITE_RULE [tenv]))) >>
     `fields = build_struct_fields_one (type_env_all_modules mods) struct_args` by
       (drule_all make_struct_fields_map_mods_lookup >>
        qpat_assum `field_key = nsid_to_string nsid` (fn name =>
          qpat_assum `registered_env.ce_struct_fields = _` (fn table =>
            qpat_assum `FLOOKUP registered_env.ce_struct_fields _ = SOME fields`
              (assume_tac o REWRITE_RULE [name,table]))) >>
        asm_rewrite_tac[optionTheory.SOME_11]) >>
     conj_tac
     >- (qpat_assum `MAP FST fields = MAP FST struct_args` SUBST1_TAC >>
         PairCases_on `nsid` >>
         `ALL_DISTINCT (MAP FST mods)` by
           (qpat_assum `contract_namespaces_ok F mods` mp_tac >>
            simp[NoAsms, contract_namespaces_ok_def]) >>
         qpat_assum `ALL_DISTINCT (MAP FST mods)` (fn distinct =>
           qpat_assum `FLOOKUP (type_env_all_modules mods) _ = SOME (StructArgs struct_args)`
             (mp_tac o REWRITE_RULE [MATCH_MP
                (Q.SPECL [`mods`,`nsid0`,`nsid1`] FLOOKUP_type_env_all_modules)
                distinct])) >>
         Cases_on `ALOOKUP mods nsid0` >> simp[NoAsms] >>
         strip_tac >>
         drule_then (CONJUNCTS_THEN2 assume_tac assume_tac) abi_caller_type_env_struct >>
         qpat_assum `ALOOKUP mods nsid0 = SOME x` (assume_tac o MATCH_MP ALOOKUP_MEM) >>
         drule_all_then ACCEPT_TAC check_contract_struct_fields_distinct) >>
     qpat_assum `fields = _` SUBST1_TAC >>
     qpat_assum `get_tenv cx = _` SUBST1_TAC >>
     simp[NoAsms, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     drule_all_then (ACCEPT_TAC o CONJUNCT2) abi_caller_struct_field_sizes) >>
  `!sid id ts tr typ id_str. get_module_code cx sid = SOME ts /\
      find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
      registered_env.ce_hashmap_info (sid,id) = NONE /\
      registered_env.ce_module_var_type (sid,id) = SOME typ` by
    (qx_genl_tac [`sid`,`id`,`ts`,`tr`,`typ`,`id_str`] >>
     disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     `ALOOKUP mods sid = SOME ts` by
       (qpat_assum `contract_inv mods exps ctx registered_env cx`
          (qspec_then `sid` (SUBST1_TAC o SYM) o MATCH_MP contract_inv_module_codes) >>
        first_assum ACCEPT_TAC) >>
     drule_all_then ACCEPT_TAC body_inv_storage_var_types_mods) >>
  qpat_assum `check_contract F cx.layouts cx.txn.target mods = SOME art`
    (strip_assume_tac o MATCH_MP check_contract_artifact_fields) >>
  `!sid. get_module_code cx sid = ALOOKUP mods sid` by
    (rpt gen_tac >> drule_then (qspec_then `sid` ACCEPT_TAC) contract_inv_module_codes) >>
  `!sid ts. ALOOKUP mods sid = SOME ts ==>
       ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel sid) ts))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `ALOOKUP mods sid = SOME ts` (assume_tac o MATCH_MP ALOOKUP_MEM) >>
     drule_all_then ACCEPT_TAC contract_namespaces_ok_module_toplevel_vtype_keys) >>
  `place_map_tables_agree_on_defined registered_env entry_types` by
    (simp[NoAsms, place_map_tables_agree_on_defined_def] >>
     qx_genl_tac [`var_key`,`vtype`] >> PairCases_on `var_key` >> strip_tac >>
     `FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes
        (var_key0,var_key1) = SOME vtype` by
       (qpat_assum `FLOOKUP entry_types.toplevel_vtypes _ = _` mp_tac >>
        qpat_assum `entry_types.toplevel_vtypes = art.cta_toplevel_vtypes` (fn entry =>
          qpat_assum `art.cta_toplevel_vtypes = _` (fn checked =>
            simp[NoAsms, entry, checked, FLOOKUP_DRESTRICT_SOME]))) >>
     drule_all build_contract_type_artifact_toplevel_vtypes_sound >>
     disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_x_assum `var_key1 = _` SUBST_ALL_TAC >>
         qpat_x_assum `vtype = Type _` SUBST_ALL_TAC >>
         drule_all_then (fn metadata => simp[NoAsms, metadata])
           contract_inv_variable_metadata) >>
     qpat_x_assum `var_key1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `vtype = HashMapT _ _` SUBST_ALL_TAC >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel var_key0) ts))` by
       (qpat_assum `!sid ts. ALOOKUP mods sid = SOME ts ==> _`
          (drule_then ACCEPT_TAC)) >>
     drule_all_then assume_tac
       (Q.INST [`src` |-> `var_key0`] find_var_decl_by_name_SOME_hashmap) >>
     `get_module_code cx var_key0 = SOME ts` by
       (qpat_assum `!sid. get_module_code cx sid = ALOOKUP mods sid`
          (qspec_then `var_key0` SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
     drule_all_then (fn info => simp[NoAsms, info]) linked_entry_hashmap_info) >>
  `!sid id ty. FLOOKUP entry_types.bare_globals (sid,id) = SOME ty ==>
    registered_env.ce_module_var_type (sid,id) = SOME ty /\
    registered_env.ce_hashmap_info (sid,id) = NONE` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (sid,id) =
        SOME ty` by
       (qpat_assum `entry_types.bare_globals = art.cta_bare_globals` (fn entry =>
          qpat_assum `art.cta_bare_globals = _` (fn checked =>
            qpat_assum `FLOOKUP entry_types.bare_globals _ = _`
              (ACCEPT_TAC o REWRITE_RULE [entry,checked])))) >>
     drule_all build_contract_type_artifact_bare_globals_sound >>
     disch_then (DISJ_CASES_THEN strip_assume_tac) >>
     qpat_x_assum `id = _` SUBST_ALL_TAC >>
     drule_all_then ACCEPT_TAC contract_inv_variable_metadata) >>
  `registered_env.ce_module = src` by
    (qpat_assum `module_body_inv mods src tops registered_env cx`
       (mp_tac o REWRITE_RULE [module_body_inv_def]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `bare_globals_complete entry_types.bare_globals cx` by
    (qpat_assum `env_context_consistent entry_types cx`
       (strip_assume_tac o REWRITE_RULE [env_context_consistent_def]) >>
     first_assum ACCEPT_TAC) >>
  `!sid id off. FLOOKUP registered_env.ce_module_vars (sid,id) = SOME (ImmutableLoc off) ==>
    ?ty. FLOOKUP entry_types.bare_globals (sid,id) = SOME ty /\
      immutable_region_mods mods sid id off
        (type_mem_bytes (get_struct_fields registered_env.ce_struct_fields) ty)` by
    (rpt gen_tac >> strip_tac >>
     drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
       contract_inv_immutable_section_layout >>
     qpat_assum `!sid id off. FLOOKUP registered_env.ce_module_vars (sid,id) = _ <=> _`
       (qspecl_then [`sid`,`id`,`off`] (fn layout =>
          qpat_assum `FLOOKUP registered_env.ce_module_vars (sid,id) = _`
            (qx_choose_then `imm_size` assume_tac o MATCH_MP (iffLR layout)))) >>
     qpat_assum `immutable_region_mods mods sid id off imm_size`
       (qx_choosel_then [`imm_table`,`imm_pre`,`imm_post`,`imm_vis`,`imm_ty`,`imm_slot`] strip_assume_tac o
        REWRITE_RULE [immutable_region_mods_def]) >>
     `get_module_code cx sid = SOME imm_table` by
       (qpat_assum `!sid. get_module_code cx sid = _` (qspec_then `sid` SUBST1_TAC) >>
        first_assum ACCEPT_TAC) >>
     `MEM (VariableDecl imm_vis Immutable id imm_ty imm_slot) imm_table` by
       (qpat_assum `imm_table = imm_pre ++ _::imm_post`
          (fn imm_table => simp[NoAsms, imm_table, MEM_APPEND])) >>
     qexists_tac `imm_ty` >> conj_tac
     >- (qpat_assum `bare_globals_complete entry_types.bare_globals cx`
           (qspecl_then [`sid`,`imm_table`,`imm_vis`,`Immutable`,`id`,`imm_ty`,`imm_slot`]
             mp_tac o REWRITE_RULE [bare_globals_complete_def]) >>
         asm_rewrite_tac[]) >>
     qpat_assum `registered_env.ce_struct_fields = _` (fn fields =>
       qpat_assum `imm_size = _` (fn size => PURE_REWRITE_TAC [fields, GSYM size])) >>
     first_assum ACCEPT_TAC) >>
  `!sid id off ty tv. FLOOKUP registered_env.ce_module_vars (sid,id) = SOME (ImmutableLoc off) /\
    FLOOKUP entry_types.bare_globals (sid,id) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    immutable_region_mods mods sid id off (type_memory_size tv)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!sid id off. FLOOKUP registered_env.ce_module_vars (sid,id) = _ ==> _`
       (drule_then (qx_choose_then `cty` strip_assume_tac)) >>
     `cty = ty` by
       (qpat_assum `FLOOKUP entry_types.bare_globals (sid,id) = SOME ty` (fn source =>
          qpat_assum `FLOOKUP entry_types.bare_globals (sid,id) = SOME cty` mp_tac >>
          simp[NoAsms, source])) >>
     qpat_x_assum `cty = ty` SUBST_ALL_TAC >>
     `get_tenv cx SUBMAP type_env_all_modules mods` by
       (qpat_assum `get_tenv cx = _` (fn tenv => simp[NoAsms, tenv])) >>
     `type_memory_bytes registered_env ty = type_memory_size tv` by
       drule_all_then ACCEPT_TAC make_struct_fields_map_mods_memory_size >>
     qpat_assum `type_memory_bytes registered_env ty = _` (SUBST1_TAC o SYM) >>
     PURE_REWRITE_TAC [GSYM type_mem_bytes_type_memory_bytes] >>
     first_assum ACCEPT_TAC) >>
  `bare_globals_layout registered_env.ce_is_ctor registered_env.ce_module_var_type
    registered_env.ce_module_vars registered_env.ce_modules cx entry_types.bare_globals
    entry_types.bare_global_assignable` by
    (PURE_REWRITE_TAC [bare_globals_layout_def] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!sid id off. FLOOKUP registered_env.ce_module_vars (sid,id) = _ ==> _`
           (drule_then (qx_choose_then `ty` strip_assume_tac)) >>
         qexists_tac `ty` >> first_assum ACCEPT_TAC)
     >- (qpat_assum `entry_types.bare_global_assignable = FEMPTY`
           (fn table => simp[NoAsms, table]))
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!sid id ty. FLOOKUP entry_types.bare_globals (sid,id) = _ ==> _`
           (drule_then (ACCEPT_TAC o CONJUNCT1)))
     >- (qx_genl_tac [`sid`,`id1`,`id2`,`ty1`,`ty2`,`off1`,`off2`,`tv1`,`tv2`] >>
         strip_tac >>
         drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
           contract_inv_immutable_section_layout >>
         `immutable_region_mods mods sid id1 off1 (type_memory_size tv1)` by
           (qpat_assum `!sid id off ty tv. FLOOKUP registered_env.ce_module_vars (sid,id) = _ /\ _ ==> _`
              (qspecl_then [`sid`,`id1`,`off1`,`ty1`,`tv1`] irule) >>
            conj_tac >- (qexists_tac `ty1` >> conj_tac >> first_assum ACCEPT_TAC) >>
            first_assum ACCEPT_TAC) >>
         `immutable_region_mods mods sid id2 off2 (type_memory_size tv2)` by
           (qpat_assum `!sid id off ty tv. FLOOKUP registered_env.ce_module_vars (sid,id) = _ /\ _ ==> _`
              (qspecl_then [`sid`,`id2`,`off2`,`ty2`,`tv2`] irule) >>
            conj_tac >- (qexists_tac `ty2` >> conj_tac >> first_assum ACCEPT_TAC) >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `!sid id off size sid' id' off' size'. (sid,id) <> (sid',id') /\ _ ==> _`
           (qspecl_then [`sid`,`id1`,`off1`,`type_memory_size tv1`,
                        `sid`,`id2`,`off2`,`type_memory_size tv2`] MATCH_MP_TAC) >>
         conj_tac
         >- (qpat_assum `id1 <> id2` (fn different => simp[NoAsms, different])) >>
         conj_tac >> first_assum ACCEPT_TAC)
     >- (qpat_assum `contract_inv mods exps ctx registered_env cx`
           (SUBST1_TAC o MATCH_MP contract_inv_cenv_modules) >>
         qpat_assum `!sid. get_module_code cx sid = _` (fn codes => simp[NoAsms, codes]))
     >- (rpt gen_tac >>
         qpat_assum `!sid. get_module_code cx sid = _` (fn codes => PURE_REWRITE_TAC [codes]) >>
         rpt strip_tac >> first_x_assum (drule_then ACCEPT_TAC)) >>
     qpat_assum `contract_inv mods exps ctx registered_env cx` (fn inv =>
       SUBST1_TAC (MATCH_MP contract_inv_cenv_modules inv) >>
       mp_tac (REWRITE_RULE [contract_inv_def] inv)) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!sid id ty. FLOOKUP entry_types.bare_globals (sid,id) = SOME ty /\
    (~cx_const_name_mods mods (sid,id) \/
     IS_SOME (FLOOKUP entry_types.bare_global_assignable (sid,id))) ==>
    (sid = entry_types.current_src ==> sid = registered_env.ce_module) /\
    (IS_SOME (FLOOKUP registered_env.ce_module_vars (sid,id)) ==>
     ?off. FLOOKUP registered_env.ce_module_vars (sid,id) = SOME (ImmutableLoc off) /\
        !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
             off + type_memory_size tv < dimword (:256))` by
    (qpat_assum `entry_types.bare_global_assignable = FEMPTY`
       (fn empty => simp[NoAsms, empty]) >>
     rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `entry_types.current_src = src` (fn env_src =>
           qpat_assum `registered_env.ce_module = src` (fn ce_src =>
             simp[NoAsms, env_src, ce_src]))) >>
     Cases_on `FLOOKUP registered_env.ce_module_vars (sid,id)` >> simp[NoAsms] >>
     Q.SUBGOAL_THEN `?off. x = ImmutableLoc off`
       (qx_choose_then `off` SUBST_ALL_TAC)
     >- (CCONTR_TAC >>
         `!off. x <> ImmutableLoc off` by
           (qpat_assum `~(?off. x = ImmutableLoc off)` mp_tac >> simp[NoAsms]) >>
        drule_all contract_inv_nonimmutable_module_location >>
        disch_then (qx_choose_then `decls` strip_assume_tac) >>
        drule_all env_consistent_bare_global_find_NONE >>
        disch_then (qx_choose_then `table` strip_assume_tac) >>
        `get_module_code cx sid = SOME decls` by
          (qpat_assum `!sid. get_module_code cx sid = ALOOKUP mods sid`
             (qspec_then `sid` SUBST1_TAC) >>
           first_assum ACCEPT_TAC) >>
        `table = decls` by
          (qpat_assum `get_module_code cx sid = SOME decls` (fn actual =>
             qpat_assum `get_module_code cx sid = SOME table` mp_tac >>
             simp[NoAsms, actual])) >>
        qpat_x_assum `table = decls` SUBST_ALL_TAC >>
        qpat_assum `find_var_decl_by_name id decls = NONE`
          (fn none => qpat_assum `find_var_decl_by_name id decls <> NONE`
            (ACCEPT_TAC o REWRITE_RULE [none]))) >>
     qexists_tac `off` >> simp[NoAsms] >>
     gen_tac >> strip_tac >>
     `immutable_region_mods mods sid id off (type_memory_size tv)` by
       (qpat_assum `!sid id off ty tv. FLOOKUP registered_env.ce_module_vars (sid,id) = _ /\ _ ==> _`
          (qspecl_then [`sid`,`id`,`off`,`ty`,`tv`] MATCH_MP_TAC) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `off + type_memory_size tv <= imm_len_mods mods` by
       (drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
          contract_inv_immutable_section_layout >>
        qpat_assum `!sid id off size. immutable_region_mods mods sid id off size ==> _`
          (drule_then ACCEPT_TAC)) >>
     irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `imm_len_mods mods` >>
     rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (irule arithmeticTheory.LESS_TRANS >> qexists_tac `24576` >>
       simp[NoAsms, dimword_def] >> first_assum ACCEPT_TAC))) >>
  `!nsid ty. FLOOKUP entry_types.bare_globals nsid = SOME ty ==>
             registered_env.ce_hashmap_info nsid = NONE` by
    (qx_genl_tac [`nsid`,`ty`] >> PairCases_on `nsid` >> strip_tac >>
     qpat_assum `!sid id ty. FLOOKUP entry_types.bare_globals (sid,id) = _ ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `expr_sim_inv_mods mods registered_env cx entry_types es` by
    (PURE_REWRITE_TAC [expr_sim_inv_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)
QED
