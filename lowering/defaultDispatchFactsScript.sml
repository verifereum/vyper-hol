(* Raw dispatch facts: the selected signature, not its name, determines placement. *)
Theory defaultDispatchFacts
Ancestors sourceEntryCode runtimeBodyStartDefs checkedSelectorTableProps entryStateRel
  vyperCalldata compileVyper vyperABIEntries publicGetterProps list entryDispatchProps
  defaultDispatchRouting defaultDispatchPlacement supportedDecls loweringShapeSource
  entrySelectedPackageCoherence calldataSourceSize

Theorem default_dispatch_raw_cases:
  calldata_dispatch tops cd = SOME (name,vals) ==>
  ((LENGTH cd < 4 \/
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = NONE) /\
   EXISTS is_default_decl tops /\ name = "__default__" /\ vals = []) \/
  (?tys tvs.
    4 <= LENGTH cd /\
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = SOME (name,tys) /\
    OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    calldata_decode_args cd tvs 0 = SOME vals)
Proof
  simp[calldata_dispatch_def] >>
  Cases_on `LENGTH cd < 4`
  >- (simp[] >> Cases_on `EXISTS is_default_decl tops` >> simp[]) >>
  simp[] >>
  Cases_on `FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops)`
  >- (simp[] >> Cases_on `EXISTS is_default_decl tops` >> simp[]) >>
  simp[] >>
  PairCases_on `x` >>
  Cases_on `OPT_MMAP (evaluate_type (type_env tops)) x1` >> simp[] >>
  Cases_on `LENGTH cd < 4 + SUM (MAP tv_abi_size x)` >> simp[] >>
  Cases_on `calldata_decode_args cd x 0` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem default_decl_signature_getter[local]:
  MEM ("__default__",tys) (abi_decl_signatures top) ==>
  ?mut nr rr args ds ret body.
    public_getter top = SOME (mut,nr,rr,"__default__",args,ds,ret,body) /\
    tys = MAP SND args
Proof
  Cases_on `public_getter top`
  >- (Cases_on `top` >>
      gvs[public_getter_def, abi_decl_signatures_def]
      >~ [`FunctionDecl vis _ _ _ _ _ _ _ _`]
      >- (Cases_on `vis` >> simp[abi_decl_signatures_def] >>
          IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP,
            pairTheory.FORALL_PROD])
      >> Cases_on `v` >> gvs[public_getter_def, abi_decl_signatures_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >> gvs[]) >>
  PairCases_on `x` >> drule public_getter_signature >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem default_signature_getter:
  MEM ("__default__",tys) (abi_external_signatures tops) ==>
  ?mut nr rr args ds ret body.
    MEM (mut,nr,rr,"__default__",args,ds,ret,body) (public_getters tops) /\
    tys = MAP SND args
Proof
  simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
  strip_tac >> gvs[] >> drule default_decl_signature_getter >> strip_tac >>
  simp[MEM_public_getters] >> metis_tac[]
QED

Theorem default_selected_source_args:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM ("__default__",tys) (abi_external_signatures tops) ==>
  tys = MAP SND args /\
  ?rr. MEM (mut,nr,rr,"__default__",args,([]:expr list),ret,fbody) (public_getters tops)
Proof
  strip_tac >>
  drule (INST_TYPE [alpha |-> ``:expr``] default_signature_getter) >> strip_tac >>
  drule_all public_getter_lookup_agrees >> gvs[] >> metis_tac[]
QED

Theorem default_selected_decode:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME ("__default__",tys) /\
  OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
  calldata_decode_args cd tvs 0 = SOME vals ==>
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
  calldata_decode_args cd tvs 0 = SOME vals
Proof
  strip_tac >>
  `MEM ("__default__",tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all default_selected_source_args >> strip_tac >> gvs[]
QED

Theorem default_dispatch_decl[local]:
  EXISTS is_default_decl tops ==>
  ?mut nr rr args ds ret fbody.
    MEM (FunctionDecl External mut nr rr "__default__" args ds ret fbody) tops
Proof
  simp[EXISTS_MEM] >> strip_tac >> Cases_on `e` >>
  gvs[is_default_decl_def] >> Cases_on `f` >> gvs[is_default_decl_def] >>
  metis_tac[]
QED

Theorem default_fallback_lookup_decl:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  ?rr. MEM (FunctionDecl External mut nr rr "__default__" args [] ret fbody) tops
Proof
  strip_tac >> drule default_dispatch_decl >> strip_tac >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
     SOME (mut',nr',args',ds,ret',fbody')` by
    (irule lookup_function_external_unique_decl >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `FunctionDecl External mut' nr' rr "__default__" args' ds ret' fbody'` >>
     simp[vyperTypeContractTheory.external_name_keys_toplevel_def,
       vyperInterpreterTheory.lookup_function_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem default_fallback_no_args:
  source_typing_ok tops am tx /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  args = []
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  drule_all default_fallback_lookup_decl >> strip_tac >>
  metis_tac[nonreentrantEntryEquivTheory.source_typing_function_header,
    supportedNamesTheory.supported_fallback_no_arguments]
QED

Theorem default_decl_no_getter:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (FunctionDecl External mut nr rr "__default__" args ds ret fbody) tops ==>
  (!nr' m ty x. ~MEM (VariableDecl (Public nr') m "__default__" ty x) tops) /\
  (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b "__default__" kt vt x) tops)
Proof
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  `MEM (NONE,"__default__")
    (external_name_keys_toplevel (NONE:num option)
      (FunctionDecl External mut nr rr "__default__" args ds ret fbody))` by
    simp[vyperTypeContractTheory.external_name_keys_toplevel_def] >>
  `F` suffices_by simp[] >>
  drule venomFnInstsProofsTheory.all_distinct_flat_map_unique >>
  strip_tac >>
  first_x_assum (qspec_then `FunctionDecl External mut nr rr "__default__" args ds ret fbody` mp_tac) >>
  simp[vyperTypeContractTheory.external_name_keys_toplevel_def]
  >- (qexists_tac `VariableDecl (Public nr') m "__default__" ty x` >>
      simp[vyperTypeContractTheory.external_name_keys_toplevel_def]) >>
  qexists_tac `HashMapDecl (Public nr') b "__default__" kt vt x` >>
  simp[vyperTypeContractTheory.external_name_keys_toplevel_def]
QED

Theorem default_fallback_classified:
  supported_program tops /\ source_typing_ok tops am tx /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  ?rr. FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,"__default__",args,([]:expr list),ret,fbody)
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  drule_all default_fallback_lookup_decl >> strip_tac >>
  drule_all default_decl_no_getter >> strip_tac >>
  `module_consts_env tops [] = []` by
    (irule supportedDeclsTheory.supported_headers_module_consts_env >>
     gvs[supportedProgramTheory.supported_program_def,
       supportedDeclsTheory.supported_declaration_headers_def] >> metis_tac[]) >>
  drule_all lookup_function_default >>
  disch_then (qspec_then `NONE` mp_tac) >> simp[]
QED

Theorem default_selected_classified_member:
  supported_program tops /\
  MEM (mut,nr,rr,name,args,(ds:expr list),ret,fbody) (public_getters tops) ==>
  MEM (mut,nr,rr,name,args,ds,ret,fbody) (FST (classify_functions tops))
Proof
  strip_tac >> drule public_getter_classified_mem >>
  `module_consts_env tops [] = []` by
    (irule supported_headers_module_consts_env >>
     gvs[supportedProgramTheory.supported_program_def,
       supported_declaration_headers_def] >> metis_tac[]) >>
  simp[constSubstTheory.subst_consts_fn_empty]
QED

Theorem default_selected_raw_return:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (mut,nr,rr,name,args,(ds:expr list),ret,fbody) (public_getters tops) ==>
  lookup_raw_return_or_F (NONE:num option) name External tops = rr
Proof
  rw[MEM_public_getters] >>
  gvs[public_getter_source_tuple] >>
  drule_all public_getter_raw_return_none >>
  simp[vyperInterpreterTheory.lookup_raw_return_or_F_def]
QED

Theorem default_decl_raw_return:
  !tops mut nr rr name args ds ret fbody.
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (FunctionDecl External mut nr rr name args ds ret fbody) tops ==>
  lookup_raw_return_or_F (NONE:num option) name External tops = rr
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h = FunctionDecl External mut nr rr name args ds ret fbody` >> gvs[]
  >- simp[vyperInterpreterTheory.lookup_raw_return_or_F_def,
       vyperInterpreterTheory.lookup_raw_return_def] >>
  `~MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) h)` by
    (gvs[ALL_DISTINCT_APPEND] >>
     `MEM (NONE,name) (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
       (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        goal_assum (drule_at Any) >>
        simp[vyperTypeContractTheory.external_name_keys_toplevel_def]) >>
     metis_tac[]) >>
  Cases_on `h` >>
  gvs[vyperInterpreterTheory.lookup_raw_return_or_F_def,
    vyperInterpreterTheory.lookup_raw_return_def,
    vyperTypeContractTheory.external_name_keys_toplevel_def,
    ALL_DISTINCT_APPEND]
  >~ [`FunctionDecl vis`] >-
    (Cases_on `vis` >>
     gvs[vyperInterpreterTheory.lookup_raw_return_def,
       vyperTypeContractTheory.external_name_keys_toplevel_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem default_dispatch_source_cases:
  supported_program tops /\ source_typing_ok tops am tx /\
  calldata_dispatch tops cd = SOME ("__default__",vals) /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  (?tvs.
    MEM (mut,F,lookup_raw_return_or_F (NONE:num option) "__default__" External tops,
      "__default__",args,([]:expr list),ret,fbody) (FST (classify_functions tops)) /\
    4 <= LENGTH cd /\
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = SOME ("__default__",MAP SND args) /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    calldata_decode_args cd tvs 0 = SOME vals) \/
  (args = [] /\ vals = [] /\
    FST (SND (SND (classify_functions tops))) =
      SOME (mut,F,lookup_raw_return_or_F (NONE:num option) "__default__" External tops,
        "__default__",[],([]:expr list),ret,fbody) /\
    (LENGTH cd < 4 \/
     FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
       (abi_external_signatures tops) = NONE))
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  drule default_dispatch_raw_cases >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (disj2_tac >> fs[] >>
      `args = []` by metis_tac[default_fallback_no_args] >> gvs[] >>
      drule_all default_fallback_classified >> strip_tac >>
      drule loweringShapePropsTheory.classify_functions_fallback_mem >> strip_tac >>
      drule_all default_decl_raw_return >> strip_tac >>
      `module_consts_env tops [] = []` by
        (irule supported_headers_module_consts_env >>
         gvs[supportedProgramTheory.supported_program_def,
           supported_declaration_headers_def] >> metis_tac[]) >>
      gvs[constSubstTheory.subst_consts_fn_empty]) >>
  disj1_tac >>
  `MEM ("__default__",tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all default_selected_source_args >> strip_tac >> gvs[] >>
  drule_all default_selected_raw_return >> strip_tac >>
  drule_all default_selected_classified_member >> strip_tac >>
  gvs[]
QED

Theorem default_external_package:
  !tops target mut rr name args ret fbody.
  ?ce pa mc pay key ut iv rt.
    set_external_package_target target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,rr,name,args,([]:expr list),ret,fbody)) =
    ("fn_" ++ name,ce,pa,mc,pay,F,key,ut,iv,fbody,rt)
Proof
  rpt gen_tac >> simp[package_external_fn_def, set_external_package_target_def]
QED

Theorem default_target_return_abi[local]:
  update_cenv_ret_abi
    (ce with <|ce_nonreentrant := nr; ce_target := target|>) ret =
  (update_cenv_ret_abi ce ret) with
    <|ce_nonreentrant := nr; ce_target := target|>
Proof
  `!sf ce ty ce'.
    ce'.ce_struct_fields = ce.ce_struct_fields /\
    ce'.ce_flag_n_members = ce.ce_flag_n_members ==>
    type_to_abi_enc_info sf ce' ty = type_to_abi_enc_info sf ce ty` by
    (recInduct type_to_abi_enc_info_ind >> rpt strip_tac >>
     drule type_memory_bytes_frame >> strip_tac >>
     simp[Ntimes type_to_abi_enc_info_def 2]
     >- (irule GENLIST_CONG >> simp[] >> rpt strip_tac >>
         first_x_assum drule >> simp[])
     >- (irule MAP_CONG >> simp[])
     >> Cases_on `FLOOKUP sf (nsid_to_string nsid)` >> simp[] >>
     irule MAP_CONG >> simp[pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `!ty. type_to_abi_enc_info ce.ce_struct_fields
    (ce with <|ce_nonreentrant := nr; ce_target := target|>) ty =
    type_to_abi_enc_info ce.ce_struct_fields ce ty` by
    (gen_tac >> first_x_assum irule >> simp[]) >>
  `!ty. type_to_abi_dec_info ce.ce_struct_fields
    (ce with <|ce_nonreentrant := nr; ce_target := target|>) ty =
    type_to_abi_dec_info ce.ce_struct_fields ce ty` by
    (gen_tac >> irule type_to_abi_dec_info_layout_cong >> simp[]) >>
  simp[update_cenv_ret_abi_def] >> Cases_on `ce` >> simp[]
QED

Theorem default_empty_package_return_layout:
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,name,[],([]:expr list),ret,fbody)) =
    (lbl,ce_ext,pa,mc,pay,F,key,ut,iv,fbody,rt) ==>
  pa = [] /\ mc = 4 /\
  ?ce_fb.
    set_fallback_package_target target
      (package_fallback_fn tops T (K global_nonreentrant_slot)
        (SOME (mut,F,rr,name,[],([]:expr list),ret,fbody))) =
      SOME (ce_fb,pay,F,key,ut,iv,fbody,rt) /\
    ce_ext = (if ret <> NoneT then update_cenv_ret_abi ce_fb ret else ce_fb) /\
    (ce_ext with <|ce_ret_enc_info := ce_fb.ce_ret_enc_info;
                  ce_ret_dec_info := ce_fb.ce_ret_dec_info;
                  ce_max_return_size := ce_fb.ce_max_return_size|>) = ce_fb /\
    ce_fb.ce_vars = FEMPTY /\ ce_fb.ce_module = NONE /\
    ~ce_fb.ce_is_ctor /\ ce_fb.ce_imm_alloca = NONE /\
    ce_fb.ce_return_pc = NONE /\ ce_fb.ce_return_buf = NONE
Proof
  simp[package_external_fn_def, package_fallback_fn_def,
    set_external_package_target_def, set_fallback_package_target_def,
    build_positional_args_def, min_calldata_size_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def] >>
  rpt strip_tac >> gvs[] >>
  simp[default_target_return_abi, update_cenv_ret_abi_def,
       build_compile_env_def, allocate_args_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem default_selected_min_size:
  source_typing_ok tops am tx /\ supported_program tops /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pa,mc,pay,F,key,ut,iv,fbody,rt) ==>
  mc = 4 + SUM (MAP tv_abi_size tvs)
Proof
  strip_tac >>
  `mc = min_calldata_size ce args 0` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     rpt strip_tac >> gvs[min_calldata_size_def]) >>
  simp[min_calldata_size_def] >> AP_TERM_TAC >>
  `LENGTH tvs = LENGTH args` by
    (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `EL x args` >> gvs[] >>
  `MEM (q,r) args` by metis_tac[MEM_EL] >>
  drule_all selected_external_package_decoder_coherent >>
  metis_tac[calldata_coherent_embedded_size]
QED

Theorem default_dispatch_cases:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  tx.function_name = "__default__" /\
  calldata_dispatch tops cd = SOME (tx.function_name,vals) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME elbl ==>
  ?lbl ce_ext ce pa mc pay key ut iv rt fallback label_st dispatch_st before checks
     st ce' body_st st'.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,ce_ext,pa,mc,pay,F,key,ut,iv,fbody,rt) /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fallback label_st = ((),dispatch_st) /\
    new_block (linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fallback) before = (before.cs_current_bb,checks) /\
    compile_entry_checks mc pay checks = ((),st) /\
    compile_register_positional_args ce pa 4 st = (ce',body_st) /\
    compile_guarded_body ce' F key ut iv fbody rt body_st = ((),st') /\
    shape_state label_st /\ shape_state dispatch_st /\ shape_state checks /\
    shape_state st /\ shape_state body_st /\ shape_state st' /\
    cs_extends label_st dispatch_st /\ cs_extends dispatch_st checks /\
    cs_extends checks st /\ cs_extends st body_st /\ cs_extends body_st st' /\
    fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
    fn_has_code st body_st func /\ fn_has_code body_st st' func /\
    label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
    label_st.cs_next_var = 0 /\
    ((ce = ce_ext /\
      runtime_selected_body_start tops rpolicy
        (lbl,ce,pa,mc,pay,F,key,ut,iv,fbody,rt) st /\
      linear_dispatch_target cd
        (MAP (\(sel,lbl,z). (sel,lbl))
          (build_selectors (type_env tops) (FST (classify_functions tops))))
        fallback = lbl /\
      (?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
        mc = 4 + SUM (MAP tv_abi_size tvs) /\ mc <= LENGTH cd /\
        calldata_decode_args cd tvs 0 = SOME vals) /\
      ?pre post. MAP (set_external_package_target rpolicy.rpol_target o
          package_external_fn tops T (K global_nonreentrant_slot))
          (FST (classify_functions tops)) =
        pre ++ (lbl,ce,pa,mc,pay,F,key,ut,iv,fbody,rt)::post /\
        ~MEM lbl (MAP FST pre) /\
        compile_external_fn_bodies pre dispatch_st = ((),before)) \/
     (ce_ext = (if ret <> NoneT then update_cenv_ret_abi ce ret else ce) /\
      (ce_ext with <|ce_ret_enc_info := ce.ce_ret_enc_info;
                    ce_ret_dec_info := ce.ce_ret_dec_info;
                    ce_max_return_size := ce.ce_max_return_size|>) = ce /\
      ce.ce_vars = FEMPTY /\
      runtime_fallback_body_start tops rpolicy
        (lbl,ce,pa,mc,pay,F,key,ut,iv,fbody,rt) st /\
      args = [] /\ vals = [] /\ pa = [] /\ mc = 4 /\
      FST (SND (SND (classify_functions tops))) =
        SOME (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
          tx.function_name,[],([]:expr list),ret,fbody) /\
      linear_dispatch_target cd
        (MAP (\(sel,lbl,z). (sel,lbl))
          (build_selectors (type_env tops) (FST (classify_functions tops))))
        fallback = fallback /\
      compile_external_fn_bodies
        (MAP (set_external_package_target rpolicy.rpol_target o
          package_external_fn tops T (K global_nonreentrant_slot))
          (FST (classify_functions tops))) dispatch_st = ((),before)))
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `mut`,
    `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`,
    `tx.function_name`, `args`, `ret`, `fbody`] strip_assume_tac default_external_package >>
  `calldata_dispatch tops cd = SOME ("__default__",vals)` by fs[] >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,F,args,([]:expr list),ret,fbody)` by metis_tac[] >>
  drule_all default_dispatch_source_cases >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac assume_tac)
  >- (`mc = 4 + SUM (MAP tv_abi_size tvs)` by
        (drule_all default_selected_min_size >> simp[]) >>
      `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
        (FST (classify_functions tops))))` by
        fs[supportedProgramTheory.supported_program_def,
          supportedNamesTheory.supported_declaration_names_def,
          supportedNamesTheory.supported_selectors_distinct_def] >>
      qpat_assum `tx.function_name = _` SUBST_ALL_TAC >>
      drule_all default_selected_compile_placement >> strip_tac >>
      drule_all default_raw_selected_target >>
      disch_then (qspec_then `fallback` assume_tac) >>
      qexistsl [`"fn_" ++ "__default__"`, `ce`, `ce`, `pa`, `mc`, `pay`, `key`,
        `ut`, `iv`, `rt`, `fallback`, `label_st`, `dispatch_st`, `before`,
        `checks`, `st`, `ce'`, `body_st`, `st'`] >>
      gvs[] >> disj1_tac >> qexistsl [`pre`, `post`] >> simp[]) >>
  qpat_assum `tx.function_name = _` SUBST_ALL_TAC >>
  fs[] >> drule_all default_empty_package_return_layout >> strip_tac >>
  `set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (FST (SND (SND (classify_functions tops))))) =
    SOME (ce_fb,pay,F,key,ut,iv,fbody,rt)` by metis_tac[] >>
  drule_all (INST_TYPE [alpha |-> ``:string``] default_fallback_compile_placement) >>
  disch_then (qspec_then `("fn___default__":string)` strip_assume_tac) >>
  `linear_dispatch_target cd
    (MAP (\(sel,lbl,z). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops))))
    fallback = fallback` by metis_tac[default_raw_fallback_target] >>
  qexistsl [`"fn_" ++ "__default__"`, `ce`, `ce_fb`, `[]`, `4`, `pay`,
    `key`, `ut`, `iv`, `rt`, `fallback`, `label_st`, `dispatch_st`,
    `opened`, `checks`, `st`, `ce_fb`, `st`, `st'`] >>
  gvs[compileEnvTheory.cs_extends_refl] >>
  (conj_tac >- (irule compileEnvTheory.cs_extends_trans >>
     qexists_tac `opened` >> simp[]) >>
   fs[runtime_fallback_body_start_def] >> metis_tac[])
QED
