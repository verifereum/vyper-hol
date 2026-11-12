Theory extRetFrameFactsPtr
Ancestors
  returnMetadataPtr supportedTypes vyperContext compileVyper compileEnv bodySim
  finite_map structFieldsProps retAbiPlanProps
  vyperTypeContract vyperInterpreter supportedDecls supportedProgram e2eDefs
  exprLowering loweringStateRelDefs

Theorem supported_return_assignable_or_empty_struct:
  supported_return_type tops ret /\ ret <> NoneT /\
  well_formed_type (type_env tops) ret ==>
  assignable_type (type_env tops) ret \/
  (?id. ret = StructT id /\ supported_struct_fields tops id = SOME [])
Proof
  strip_tac >>
  Cases_on `?id. ret = StructT id /\ supported_struct_fields tops id = SOME []`
  >- simp[] >>
  disj1_tac >> irule supported_return_type_assignable >>
  simp[] >> metis_tac[]
QED

Theorem empty_struct_return_encoding:
  FLOOKUP cenv.ce_struct_fields (nsid_to_string id) = SOME [] ==>
  type_to_abi_enc_info cenv.ce_struct_fields cenv (StructT id) = AbiCopy 0
Proof
  strip_tac >>
  simp[Once type_to_abi_enc_info_def, is_abi_dynamic_def,
       type_memory_bytes_def, get_struct_fields_def]
QED

Theorem build_external_return_buf_none[local]:
  (build_compile_env tops External mut name args ret fbody use_trans).ce_return_buf = NONE
Proof
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem external_frame_control_metadata:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, F, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr, key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  next.ce_return_pc = NONE /\ next.ce_return_buf = NONE /\
  next.ce_ctor_exit_label = NONE /\
  next.ce_nonreentrant = (F, keys name, use_trans, mut = View) /\
  next.ce_raw_return = rr
Proof
  strip_tac >> drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_external_no_return_pc] >>
  strip_tac >> gvs[build_compile_env_external_no_return_pc,
                       build_external_return_buf_none]
QED

Theorem consistent_empty_struct_lookup:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv id = SOME (StructArgs []) ==>
  FLOOKUP sf (nsid_to_string id) = SOME []
Proof
  rw[sfields_tenv_consistent_def] >>
  first_x_assum drule >> simp[]
QED

Theorem supported_empty_struct_map_lookup:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_struct_fields tops id = SOME [] ==>
  FLOOKUP (make_struct_fields_map tops) (nsid_to_string id) = SOME []
Proof
  strip_tac >> drule make_struct_fields_map_consistent >> strip_tac >>
  drule supported_struct_fields_type_env >> strip_tac >>
  irule consistent_empty_struct_lookup >> simp[] >> metis_tac[]
QED

Theorem supported_lookup_external_raw_decl:
  !ts ambient name mut nr args defaults ret body.
  EVERY (supported_declaration_header ambient) ts /\
  lookup_function (NONE : num option) name External ts =
    SOME (mut,nr,args,defaults,ret,body) ==>
  ?rr. MEM (FunctionDecl External mut nr rr name args defaults ret body) ts /\
       lookup_raw_return (NONE : num option) name External ts = SOME rr
Proof
  Induct_on `ts` >- simp[lookup_function_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM] >>
      Cases_on `s = name /\ f = External` >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >>
      simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM, supported_public_variables_rejected] >>
      metis_tac[])
  >- (simp[listTheory.EVERY_DEF, supported_hashmap_header_contract] >>
      strip_tac >> gvs[lookup_function_def, lookup_raw_return_def,
                      listTheory.MEM] >> metis_tac[])
  >> simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
          listTheory.MEM] >> metis_tac[]
QED

Theorem check_contract_raw_return_type:
  !in_deploy layouts addr mods art src tls vis mut nr name args defaults ret body.
  check_contract in_deploy layouts addr mods = SOME art /\
  MEM (src,tls) mods /\
  MEM (FunctionDecl vis mut nr T name args defaults ret body) tls ==>
  ?n. ret = BaseT (BytesT (Dynamic n))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x mods ==> check_module _ _ _ _ _ _ x` drule >>
  simp[check_module_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x tls ==> check_toplevel_decl _ _ _ x` drule >>
  simp[check_toplevel_decl_def, function_header_ok_def]
QED

Theorem source_typing_raw_return_type:
  !tops am tx mut nr args defaults ret body.
  source_typing_ok tops am tx /\ supported_program tops /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,defaults,ret,body) /\
  lookup_raw_return_or_F (NONE : num option) tx.function_name External tops ==>
  ?n. ret = BaseT (BytesT (Dynamic n))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  drule_all supported_lookup_external_raw_decl >> strip_tac >>
  gvs[lookup_raw_return_or_F_def, source_typing_ok_def] >>
  drule check_contract_raw_return_type >> simp[listTheory.MEM] >>
  metis_tac[]
QED

Theorem external_frame_empty_struct_encoder:
  !tops target use_trans keys mut nr rr name args defaults id body
   lbl cenv0 pos cds payable nr' key ut view body' rt off st cenv sa next.
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_struct_fields tops id = SOME [] /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,StructT id,body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next ==>
  next.ce_ret_enc_info = AbiCopy 0
Proof
  rpt gen_tac >> strip_tac >>
  drule_all supported_empty_struct_map_lookup >> strip_tac >>
  `next.ce_ret_enc_info = cenv0.ce_ret_enc_info` by
    (drule_all register_same_frame_metadata >>
     simp[compile_env_component_equality]) >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `same_frame _ _` kall_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_ce_struct_fields] >>
  strip_tac >> gvs[is_abi_dynamic_def, get_struct_fields_def] >>
  simp[Once type_to_abi_enc_info_def, is_abi_dynamic_def,
       type_memory_bytes_def, get_struct_fields_def,
       build_compile_env_ce_struct_fields]
QED
