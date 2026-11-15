(* Buffer bounds for packaged external functions and actual fallbacks. *)
Theory externalReturnBuffer
Ancestors
  compileVyper moduleLowering supportedProgram supportedNames supportedDecls
  entryDispatchProps entryStateRel e2eDefs publicGetterProps
  list pair compileEnv exprLowering constSubst vyperInterpreter

val _ = Parse.hide "body";

Theorem build_compile_env_return_buffer_ok:
  !tops vis mut name args ret body use_trans.
    return_buffer_ok
      (build_compile_env tops vis mut name args ret body use_trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[return_buffer_ok_def]
QED

Theorem update_cenv_ret_abi_word_return_buffer_ok:
  !cenv ret. is_word_type ret ==>
    return_buffer_ok (update_cenv_ret_abi cenv ret)
Proof
  Cases_on `ret` >> simp[is_word_type_def] >-
    (Cases_on `b` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def] >>
     rename1 `BytesT kind` >> Cases_on `kind` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def]) >>
  simp[update_cenv_ret_abi_def, return_buffer_ok_def,
       type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
       abi_static_size_def, type_memory_bytes_def]
QED

Theorem package_external_fn_return_buffer_ok:
  !target tops use_trans nkeys mut nr rr name args dflts ret body'
   lbl cenv pos_args min_cds is_payable nr' nkey ut iv body rt.
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,dflts,ret,body')) =
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) /\
  external_return_buffer_ok
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) ==>
  (stmts_valued_return body /\ ~cenv.ce_raw_return ==>
    return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ret = NoneT`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      `return_buffer_ok
         (build_compile_env tops External mut name args ret body' use_trans)`
        by irule build_compile_env_return_buffer_ok >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  Cases_on `is_word_type ret`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      drule update_cenv_ret_abi_word_return_buffer_ok >>
      disch_then (qspec_then
        `build_compile_env tops External mut name args ret body' use_trans
           with ce_raw_return := rr` mp_tac) >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  gvs[package_external_fn_def, set_external_package_target_def,
      external_return_buffer_ok_def]
QED

(* The fallback and external packages share the same environment and return
   metadata; only dispatch metadata differs. *)
Theorem buffer_fallback_check[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops =
    (exts,ints,SOME (mut,nr,rr,name,args,defaults,ret,body),ctor) ==>
  external_return_buffer_ok
    (set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,nr,rr,name,args,defaults,ret,body)))
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  strip_tac >>
  qpat_x_assum `OPTION_ALL _ _` mp_tac >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       package_external_fn_def, set_external_package_target_def,
       external_return_buffer_ok_def] >>
  Cases_on `ret = NoneT` >> simp[]
QED

Theorem external_default_return_buffer_ok:
  !tops rpolicy unit tx ret mut args fbody lbl cenv0 pos_args
   min_cds is_payable nkey ut iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    tx.function_name = "__default__" /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,[],ret,fbody)) =
      (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
    (stmts_valued_return fbody /\ cenv.ce_is_external /\
     ~cenv.ce_raw_return ==> return_buffer_ok cenv)
Proof
  rpt strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST_ALL_TAC >>
  fs[return_buffer_ok_def] >>
  `~cenv0.ce_raw_return` by gvs[] >>
  `return_buffer_ok cenv0` suffices_by gvs[return_buffer_ok_def] >>
  `external_return_buffer_ok
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt)` suffices_by
    (strip_tac >> drule_all package_external_fn_return_buffer_ok >> simp[]) >>
  (* Supported names do not imply distinct getter/declaration names. Recover
     the selected raw flag from the package, rather than assuming raw lookup
     is absent merely because this provenance branch is a getter. *)
  `~lookup_raw_return_or_F (NONE : num option)
      tx.function_name External tops` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def] >>
     Cases_on `ret = NoneT` >>
     gvs[update_cenv_ret_abi_def] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `set_external_package_target _ _ = _`
    (SUBST1_TAC o SYM) >>
  drule lookup_function_external_raw_cases >> strip_tac
  >- (Cases_on `classify_functions tops` >> PairCases_on `r` >>
      `r1 = SOME (mut,F,rr,"__default__",args,[],ret,fbody)` by
        (drule_all supported_external_classification >> gvs[]) >>
      `lookup_raw_return_or_F (NONE : num option) tx.function_name External tops = rr` by
        gvs[lookup_raw_return_or_F_def] >>
      gvs[] >> drule_all buffer_fallback_check >>
      simp[package_external_fn_def]) >>
  `MEM (mut,F,F,tx.function_name,args,([] : expr list),ret,fbody)
       (public_getters tops)` by
    (simp[MEM_public_getters] >> qexists `decl` >>
     gvs[public_getter_source_tuple]) >>
  drule public_getter_classified_mem >>
  `module_consts_env tops [] = []` by
    metis_tac[supported_program_def, supported_declaration_headers_def,
              supported_headers_module_consts_env] >>
  simp[subst_consts_fn_empty] >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >> fs[] >>
  drule_all lower_vyper_runtime_unit_return_buffer_ok >>
  simp[package_external_fn_def]
QED
