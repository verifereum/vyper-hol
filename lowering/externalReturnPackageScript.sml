Theory externalReturnPackage
Ancestors
  entryStateRel bodySim retAbiPlanProps compileVyper compileEnv moduleLowering exprLowering supportedProgram supportedDecls entryDispatchProps

val _ = Parse.hide "body";

Theorem return_package_metadata:
  package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) ==>
  cenv.ce_raw_return = rr /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_type_env = type_env tops /\
  cenv.ce_nonreentrant = (nr,nkey_map fname,use_trans,mut = View) /\
  cenv.ce_is_external /\ ~cenv.ce_is_ctor /\
  cenv.ce_return_pc = NONE /\
  cenv.ce_ret_enc_info =
    (if ret = NoneT then AbiPrimWord else
      (update_cenv_ret_abi
        ((build_compile_env tops External mut fname fargs ret fbody use_trans)
          with ce_raw_return := rr) ret).ce_ret_enc_info) /\
  cenv.ce_max_return_size =
    (if ret = NoneT then 0 else
      (update_cenv_ret_abi
        ((build_compile_env tops External mut fname fargs ret fbody use_trans)
          with ce_raw_return := rr) ret).ce_max_return_size) /\
  rt = (if ret = NoneT then NONE else SOME ret) /\
  nr' = nr /\ nkey = nkey_map fname /\ ut = use_trans /\ iv = (mut = View)
Proof
  Cases_on `ret = NoneT` >>
  simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >> simp[update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem return_package_target_inversion:
  set_external_package_target target package =
    (lbl,cenv,pos_args,min_cds,is_payable,nr,nkey,ut,iv,body,rt) ==>
  ?cenv0.
    package = (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,body,rt) /\
    cenv = cenv0 with ce_target := target
Proof
  PairCases_on `package` >>
  simp[set_external_package_target_def] >> rpt strip_tac >> gvs[]
QED

Theorem return_register_metadata:
  compile_register_positional_args cenv args off st = (cenv',st') ==>
  cenv'.ce_raw_return = cenv.ce_raw_return /\
  cenv'.ce_struct_fields = cenv.ce_struct_fields /\
  cenv'.ce_type_env = cenv.ce_type_env /\
  cenv'.ce_nonreentrant = cenv.ce_nonreentrant /\
  cenv'.ce_is_external = cenv.ce_is_external /\
  cenv'.ce_is_ctor = cenv.ce_is_ctor /\
  cenv'.ce_ret_enc_info = cenv.ce_ret_enc_info /\
  cenv'.ce_max_return_size = cenv.ce_max_return_size /\
  cenv'.ce_target = cenv.ce_target /\
  cenv'.ce_return_pc = cenv.ce_return_pc
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem return_same_frame_metadata:
  same_frame cenv cenv' ==>
  cenv'.ce_raw_return = cenv.ce_raw_return /\
  cenv'.ce_struct_fields = cenv.ce_struct_fields /\
  cenv'.ce_type_env = cenv.ce_type_env /\
  cenv'.ce_nonreentrant = cenv.ce_nonreentrant /\
  cenv'.ce_is_external = cenv.ce_is_external /\
  cenv'.ce_is_ctor = cenv.ce_is_ctor /\
  cenv'.ce_ret_enc_info = cenv.ce_ret_enc_info /\
  cenv'.ce_max_return_size = cenv.ce_max_return_size /\
  cenv'.ce_target = cenv.ce_target /\
  cenv'.ce_return_pc = cenv.ce_return_pc
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem return_selected_frame_mode:
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  cenv.ce_raw_return = rr /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_type_env = type_env tops /\
  cenv.ce_nonreentrant = (F,nkey,F,mut = View) /\
  cenv.ce_is_external /\ ~cenv.ce_is_ctor /\
  cenv.ce_return_pc = NONE /\ cenv.ce_target = target /\
  rt = (if ret = NoneT then NONE else SOME ret)
Proof
  strip_tac >> drule return_package_target_inversion >> strip_tac >>
  drule return_package_metadata >> strip_tac >>
  drule return_register_metadata >> strip_tac >> gvs[]
QED

Theorem return_selected_frame_encoding:
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  cenv.ce_ret_enc_info =
    (if ret = NoneT then AbiPrimWord else
      (update_cenv_ret_abi
        ((build_compile_env tops External mut fname args ret fbody F)
          with ce_raw_return := rr) ret).ce_ret_enc_info) /\
  cenv.ce_max_return_size =
    (if ret = NoneT then 0 else
      (update_cenv_ret_abi
        ((build_compile_env tops External mut fname args ret fbody F)
          with ce_raw_return := rr) ret).ce_max_return_size)
Proof
  strip_tac >> drule return_package_target_inversion >> strip_tac >>
  drule return_package_metadata >> strip_tac >>
  drule return_register_metadata >> strip_tac >> gvs[]
QED

Theorem return_selected_same_frame_mode:
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv cenv' ==>
  cenv'.ce_raw_return = rr /\
  cenv'.ce_struct_fields = make_struct_fields_map tops /\
  cenv'.ce_type_env = type_env tops /\
  cenv'.ce_nonreentrant = (F,nkey,F,mut = View) /\
  cenv'.ce_is_external /\ ~cenv'.ce_is_ctor /\
  cenv'.ce_return_pc = NONE /\ cenv'.ce_target = target
Proof
  strip_tac >> drule_all return_selected_frame_mode >> strip_tac >>
  drule return_same_frame_metadata >> strip_tac >> gvs[]
QED

(* Evaluation, unlike assignability, also admits empty static aggregates. *)
Theorem return_static_evaluated_plan:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) /\
  evaluate_type tenv ty = SOME tv /\ ty <> NoneT /\
  ~is_abi_dynamic cenv.ce_struct_fields ty ==>
  abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  strip_tac >>
  `type_to_abi_enc_info sf cenv ty = AbiCopy (type_memory_bytes cenv ty)` by
    (Cases_on `ty` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]
     >- (rename1 `BaseT bt` >> Cases_on `bt` >>
         gvs[type_to_abi_enc_info_def, is_abi_dynamic_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]) >>
     rename1 `ArrayT elem bd` >> Cases_on `bd` >>
     gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]) >>
  simp[] >> irule abi_enc_plan_static_copy >> metis_tac[]
QED

Theorem return_fn_alloc_size:
  fn_allocs_ok tops (mut,nr,rr,fname,args,dflts,ret,ss) /\
  cenv.ce_struct_fields = make_struct_fields_map tops ==>
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >> qmatch_asmsub_abbrev_tac `fn_allocs_ok tops f` >>
  fs[fn_allocs_ok_def, Abbr `f`] >>
  qmatch_asmsub_abbrev_tac `type_memory_bytes c ret` >>
  `cenv.ce_struct_fields = c.ce_struct_fields` by
    simp[Abbr `c`, build_compile_env_ce_struct_fields] >>
  drule type_memory_bytes_frame >> simp[]
QED

Theorem return_runtime_function_size:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  (MEM (mut,nr,rr,fname,args,dflts,ret,ss) exts \/
   MEM (mut,nr,rr,fname,args,dflts,ret,ss) ints \/
   fb = SOME (mut,nr,rr,fname,args,dflts,ret,ss)) /\
  cenv.ce_struct_fields = make_struct_fields_map tops ==>
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >>
  `fn_allocs_ok tops (mut,nr,rr,fname,args,dflts,ret,ss)` by
    (irule lower_vyper_runtime_unit_allocs_ok >> metis_tac[]) >>
  drule_all return_fn_alloc_size >> simp[]
QED

Theorem return_supported_no_getters[local]:
  supported_program tops ==>
  (!nr mut ty slot. ~MEM (VariableDecl (Public nr) mut name ty slot) tops) /\
  (!nr tr kt vt slot. ~MEM (HashMapDecl (Public nr) tr name kt vt slot) tops)
Proof
  strip_tac >> conj_tac >> rpt strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def]
QED

Theorem return_selected_lookup_size:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  lookup_function NONE name External tops = SOME (mut,nr,args,dflts,ret,fbody) /\
  cenv.ce_struct_fields = make_struct_fields_map tops ==>
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >>
  `(!nr mut ty slot. ~MEM (VariableDecl (Public nr) mut name ty slot) tops) /\
   (!nr tr kt vt slot. ~MEM (HashMapDecl (Public nr) tr name kt vt slot) tops)` by
    metis_tac[return_supported_no_getters] >>
  Cases_on `name = "__default__"`
  >- (gvs[] >> drule_all lookup_function_default >>
      disch_then (qspec_then `NONE` mp_tac) >>
      Cases_on `classify_functions tops` >> PairCases_on `r` >> simp[] >>
      Cases_on `r1` >> simp[] >> PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >>
      irule (SRULE [] return_runtime_function_size) >> metis_tac[]) >>
  drule_all lookup_function_external_mem >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
  irule (SRULE [] return_runtime_function_size) >> metis_tac[]
QED

Theorem return_selected_package_size:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  type_memory_bytes cenv ret < 2 ** 64
Proof
  strip_tac >> drule_all return_selected_frame_mode >> strip_tac >>
  drule_all return_selected_lookup_size >> simp[]
QED
