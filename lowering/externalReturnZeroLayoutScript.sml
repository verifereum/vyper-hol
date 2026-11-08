(* Evaluated empty source layouts are ABI-static. *)
Theory externalReturnZeroLayout
Ancestors
  retAbiPlanProps compileVyper exprLoweringProps entryStateRel bodySim stmtSimDefs exprLowering compileEnv valueEncodingProofs valueEncodingProps vyperABI vyperValue valueEncoding
  vyperTypeSystem vyperTypeABI valueEncodingTyping list finite_map option

Theorem evaluated_zero_layout_static_joint[local]:
  (!env ty. (!tv. evaluate_type env ty = SOME tv /\
      type_memory_size tv = 0 ==> ~vyper_is_dynamic env ty)) /\
  (!env ts acc. (!tvs. evaluate_types env ts acc = SOME tvs /\
      type_memory_size_list tvs = 0 ==> ~vyper_any_dynamic env ts))
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def,
      vyper_is_dynamic_def]
  >~ [`type_memory_size (ArrayTV tv bd) = 0`]
  >- (Cases_on `bd` >> gvs[type_memory_size_def,
                         vyper_is_dynamic_def])
  >~ [`type_memory_size_fields (ZIP (MAP FST args,tvs)) = 0`]
  >- (`LENGTH args = LENGTH tvs` by
        (gvs[evaluate_types_OPT_MMAP] >> drule OPT_MMAP_LENGTH >> simp[]) >>
      `type_memory_size_fields (ZIP (MAP FST args,tvs)) =
       type_memory_size_list tvs` by
        (irule type_memory_size_fields_zip >> simp[]) >> gvs[]) >>
  gvs[evaluate_types_OPT_MMAP, AllCaseEqs(), type_memory_size_list_sum,
      MAP_APPEND, MAP_REVERSE, SUM_APPEND]
QED

Theorem evaluated_zero_layout_static:
  evaluate_type env ty = SOME tv /\ type_memory_size tv = 0 ==>
  ~vyper_is_dynamic env ty
Proof
  metis_tac[evaluated_zero_layout_static_joint]
QED

Theorem evaluated_zero_layout_compiler_static:
  evaluate_type env ty = SOME tv /\ type_memory_size tv = 0 /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env /\
  (!k a. FLOOKUP env k = SOME (StructArgs a) ==> FST k = NONE) ==>
  ~is_abi_dynamic sf ty
Proof
  strip_tac >> drule_all evaluated_zero_layout_static >> strip_tac >>
  drule (cj 1 abi_props_vyper) >> disch_then drule_all >>
  simp[]
QED

Theorem zero_layout_encoder_info:
  evaluate_type env ty = SOME tv /\ type_memory_size tv = 0 /\
  sfields_tenv_consistent cenv.ce_struct_fields env /\
  (!k a. FLOOKUP env k = SOME (StructArgs a) ==> FST k = NONE) /\
  type_memory_bytes cenv ty = type_memory_size tv /\ ty <> NoneT ==>
  type_to_abi_enc_info cenv.ce_struct_fields cenv ty = AbiCopy 0
Proof
  strip_tac >> drule_all evaluated_zero_layout_compiler_static >> strip_tac >>
  Cases_on `ty` >>
  gvs[type_to_abi_enc_info_def, is_abi_dynamic_def, evaluate_type_def,
      AllCaseEqs(), type_memory_size_def] >>
  Cases_on `b` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def,
                      type_memory_size_def]
QED

Theorem zero_layout_return_metadata:
  evaluate_type env ty = SOME tv /\ type_memory_size tv = 0 /\
  sfields_tenv_consistent cenv.ce_struct_fields env /\
  (!k a. FLOOKUP env k = SOME (StructArgs a) ==> FST k = NONE) /\
  type_memory_bytes cenv ty = type_memory_size tv /\ ty <> NoneT ==>
  (update_cenv_ret_abi cenv ty).ce_ret_enc_info = AbiCopy 0
Proof
  strip_tac >> drule_all zero_layout_encoder_info >> strip_tac >>
  drule_all evaluated_zero_layout_compiler_static >> strip_tac >>
  simp[update_cenv_ret_abi_def]
QED

Theorem valued_return_type_not_none:
  IS_SOME (type_stmt env ret (Return (SOME e))) ==> ret <> NoneT
Proof
  simp[type_stmt_def, AllCaseEqs()]
QED

Theorem external_package_return_encoder:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
      (mut,nr0,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr,nkey,ut,iv,body',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv cenv' /\ ret <> NoneT ==>
  cenv'.ce_ret_enc_info =
    (update_cenv_ret_abi
      (build_compile_env tops External mut fname fargs ret fbody ut0
        with ce_raw_return := rr) ret).ce_ret_enc_info
Proof
  strip_tac >>
  `cenv0.ce_ret_enc_info =
    (update_cenv_ret_abi
      (build_compile_env tops External mut fname fargs ret fbody ut0
        with ce_raw_return := rr) ret).ce_ret_enc_info` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def] >> strip_tac >> gvs[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  fs[same_frame_def] >>
  `cenv'.ce_ret_enc_info = cenv.ce_ret_enc_info` by
    (qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `cenv.ce_ret_enc_info = cenv0.ce_ret_enc_info` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >> simp[]
QED

Theorem external_package_zero_layout_encoder:
  set_external_package_target tgt
    (package_external_fn tops ut0 nkm
      (mut,nr0,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,payable,nr,nkey,ut,iv,body',rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv cenv' /\ IS_SOME (type_stmt env ret (Return (SOME e))) /\
  ce_base = build_compile_env tops External mut fname fargs ret fbody ut0 /\
  evaluate_type tenv ret = SOME tv /\ type_memory_size tv = 0 /\
  sfields_tenv_consistent ce_base.ce_struct_fields tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  type_memory_bytes ce_base ret = type_memory_size tv ==>
  cenv'.ce_ret_enc_info = AbiCopy 0
Proof
  strip_tac >> drule valued_return_type_not_none >> strip_tac >>
  drule_all external_package_return_encoder >> strip_tac >>
  `type_memory_bytes (ce_base with ce_raw_return := rr) ret =
     type_memory_bytes ce_base ret` by (irule type_memory_bytes_struct_fields >> simp[]) >>
  `sfields_tenv_consistent (ce_base with ce_raw_return := rr).ce_struct_fields tenv`
    by (qpat_x_assum `ce_base = _` SUBST_ALL_TAC >> fs[]) >>
  ` (update_cenv_ret_abi (ce_base with ce_raw_return := rr) ret).ce_ret_enc_info =
      AbiCopy 0` by
    (irule zero_layout_return_metadata >> simp[] >> qexistsl_tac [`tenv`,`tv`] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `ce_base = _` SUBST_ALL_TAC >> fs[]) >> gvs[]
QED
