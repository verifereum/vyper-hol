(* TOP-LEVEL: source and compiler metadata agree on ABI dynamic shape for
   every evaluated type. Struct lookup correspondence survives the matching
   cycle guards. Helpers compose list, tuple and fixed-array classifications. *)
Theory abiTypeShape
Ancestors
  structSourceProps typeLayoutProps exprLowering compileVyper compileEnv
  vyperABI vyperValue vyperAST vyperContext vyperTypeABI vyperTypeValues
  sourceAbiTypingLists contractABI finite_map list pair combin words

Definition abi_struct_env_rel_def:
  abi_struct_env_rel tenv (sfields:(string, (string # type # num) list) fmap) <=>
    !nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==>
      FST nsid = NONE /\ ?fields. FLOOKUP sfields (nsid_to_string nsid) = SOME fields /\
        MAP (FST o SND) fields = MAP SND args
End

Theorem abi_struct_env_rel_lookup:
  !tenv sfields nsid args.
    abi_struct_env_rel tenv sfields /\ FLOOKUP tenv nsid = SOME (StructArgs args) ==>
    FST nsid = NONE /\ ?fields. FLOOKUP sfields (nsid_to_string nsid) = SOME fields /\
      MAP (FST o SND) fields = MAP SND args
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `abi_struct_env_rel _ _` (mp_tac o REWRITE_RULE [abi_struct_env_rel_def]) >>
  disch_then (qspecl_then [`nsid`, `args`] mp_tac) >> simp[]
QED

Theorem abi_struct_env_rel_domsub:
  !tenv sfields nsid.
    abi_struct_env_rel tenv sfields /\ FST nsid = NONE ==>
    abi_struct_env_rel (tenv \\ nsid) (sfields \\ nsid_to_string nsid)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_struct_env_rel_def] >>
  MAP_EVERY qx_gen_tac [`other_id`, `args`] >> DISCH_TAC >>
  `other_id <> nsid /\ FLOOKUP tenv other_id = SOME (StructArgs args)` by
    (Cases_on `other_id = nsid` >> gvs[DOMSUB_FLOOKUP_THM]) >>
  drule_all abi_struct_env_rel_lookup >> strip_tac >>
  `nsid_to_string other_id <> nsid_to_string nsid` by
    (Cases_on `other_id` >> Cases_on `nsid` >> gvs[nsid_to_string_def]) >>
  simp_tac bool_ss [] >> goal_assum drule >> simp[DOMSUB_FLOOKUP_THM]
QED

Theorem abi_struct_env_rel_tops:
  !tops. struct_args_unique tops ==> abi_struct_env_rel (type_env tops) (make_struct_fields_map tops)
Proof
  gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_struct_env_rel_def] >>
  MAP_EVERY qx_gen_tac [`nsid`, `args`] >> DISCH_TAC >>
  `FLOOKUP (type_env_for_module NONE tops) nsid = SOME (StructArgs args)` by fs[type_env_def] >>
  `FST nsid = NONE` by (drule type_env_for_module_struct_origin >> strip_tac >> simp[]) >>
  drule_all evaluated_struct_metadata_types >> simp[]
QED

Theorem abi_base_dynamic:
  !sfields bt.
    is_abi_dynamic sfields (BaseT bt) = is_dynamic (vyper_base_to_abi_type bt)
Proof
  rpt gen_tac >> Cases_on `bt` >> simp[is_abi_dynamic_def, vyper_base_to_abi_type_def, is_dynamic_def] >>
  qmatch_goalsub_rename_tac `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[is_abi_dynamic_def, vyper_base_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_dynamic_exists:
  !tys left right.
    EVERY (\ty. left ty = right ty) tys ==> (EXISTS left tys = EXISTS right tys)
Proof
  Induct_on `tys` >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`left`, `right`] mp_tac) >> simp[]
QED

Theorem abi_dynamic_tuple_case:
  !tenv tys.
    (!sfields tvs. abi_struct_env_rel tenv sfields /\
      LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
      EVERY (\ty. is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) tys) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (TupleT tys) = SOME tv ==>
      is_abi_dynamic sfields (TupleT tys) = is_dynamic (vyper_to_abi_type tenv (TupleT tys))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_TupleT_cases >> strip_tac >> first_x_assum drule_all >> DISCH_TAC >>
  `EXISTS (is_abi_dynamic sfields) tys = EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys` by
    (irule abi_dynamic_exists >> simp[]) >>
  asm_simp_tac (srw_ss()) [Once is_abi_dynamic_def, Once vyper_to_abi_type_def,
    is_dynamic_def, any_dynamic_EXISTS, source_abi_types_map, EXISTS_MAP] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []
QED

Theorem abi_dynamic_fixed_array_case:
  !tenv elem count.
    (!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv elem = SOME tv ==>
      is_abi_dynamic sfields elem = is_dynamic (vyper_to_abi_type tenv elem)) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (ArrayT elem (Fixed count)) = SOME tv ==>
      is_abi_dynamic sfields (ArrayT elem (Fixed count)) =
        is_dynamic (vyper_to_abi_type tenv (ArrayT elem (Fixed count)))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> first_x_assum drule_all >> DISCH_TAC >>
  asm_simp_tac (srw_ss()) [Once is_abi_dynamic_def, Once vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_dynamic_struct_case:
  !tenv nsid.
    (!arg_kind args. FLOOKUP tenv nsid = SOME arg_kind /\ arg_kind = StructArgs args ==>
      !sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\
        LIST_REL (\ty tv. evaluate_type (tenv \\ nsid) ty = SOME tv) (MAP SND args) tvs ==>
        EVERY (\ty. is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type (tenv \\ nsid) ty)) (MAP SND args)) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (StructT nsid) = SOME tv ==>
      is_abi_dynamic sfields (StructT nsid) = is_dynamic (vyper_to_abi_type tenv (StructT nsid))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `evaluate_type _ _ = _` (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs source_args)` >>
  rename1 `evaluate_types (tenv \\ nsid) (MAP SND source_args) [] = SOME field_tvs` >>
  drule_all abi_struct_env_rel_lookup >> strip_tac >>
  drule_all abi_struct_env_rel_domsub >> DISCH_TAC >>
  drule evaluate_types_LIST_REL >> DISCH_TAC >>
  qpat_x_assum `!sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\ _ ==> _`
    (qspecl_then [`sfields \\ nsid_to_string nsid`, `field_tvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `EXISTS (is_abi_dynamic (sfields \\ nsid_to_string nsid)) (MAP SND source_args) =
    EXISTS (\ty. is_dynamic (vyper_to_abi_type (tenv \\ nsid) ty)) (MAP SND source_args)` by
    (irule abi_dynamic_exists >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [is_abi_dynamic_def])) >>
  asm_simp_tac bool_ss [LET_THM] >>
  asm_simp_tac (srw_ss()) [any_dynamic_EXISTS, source_abi_types_map, EXISTS_MAP] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `MAP (FST o SND) fields = MAP SND source_args`
    (mp_tac o AP_TERM ``EXISTS (is_abi_dynamic
      ((sfields:(string, (string # type # num) list) fmap) \\ nsid_to_string nsid))``) >>
  qpat_x_assum `EXISTS (is_abi_dynamic _) (MAP SND source_args) = _`
    (mp_tac o REWRITE_RULE [EXISTS_MAP]) >>
  simp[EXISTS_MAP, o_DEF] >> rpt strip_tac >> gvs[]
QED

Theorem abi_dynamic_cons_case:
  !tenv ty tys.
    ((!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
       is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) /\
     (!sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
       EVERY (\ty. is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) tys)) ==>
    !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (ty::tys) tvs ==>
      EVERY (\ty. is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) (ty::tys)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_type_dynamic_joint:
  (!tenv ty. !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
    is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) /\
  (!tenv tys. !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    EVERY (\ty. is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type tenv ty)) tys)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac >|
    [simp[abi_base_dynamic],
     MATCH_ACCEPT_TAC abi_dynamic_tuple_case,
     simp[Once is_abi_dynamic_def, Once vyper_to_abi_type_def, is_dynamic_def],
     MATCH_ACCEPT_TAC abi_dynamic_fixed_array_case,
     MATCH_ACCEPT_TAC abi_dynamic_struct_case,
     simp[is_abi_dynamic_def, is_dynamic_def],
     simp[is_abi_dynamic_def, is_dynamic_def],
     simp[],
     MATCH_ACCEPT_TAC abi_dynamic_cons_case]
QED

Theorem evaluated_abi_type_dynamic:
  !tops sfields ty tv.
    struct_args_unique tops /\ sfields = make_struct_fields_map tops /\ evaluate_type (type_env tops) ty = SOME tv ==>
    is_abi_dynamic sfields ty = is_dynamic (vyper_to_abi_type (type_env tops) ty)
Proof
  rpt gen_tac >> strip_tac >> drule abi_struct_env_rel_tops >> DISCH_TAC >>
  mp_tac (Q.SPECL [`type_env tops`, `ty`, `sfields`, `tv`] (CONJUNCT1 abi_type_dynamic_joint)) >> simp[]
QED

Theorem evaluated_static_tuple_info:
  !tops cenv tys tvs.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) tys tvs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type (type_env tops) ty)) tys ==>
    type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) = AbiCopy (type_memory_size_list tvs)
Proof
  rpt gen_tac >> strip_tac >> drule abi_struct_env_rel_tops >> DISCH_TAC >>
  mp_tac (Q.SPECL [`type_env tops`, `tys`, `make_struct_fields_map tops`, `tvs`] (CONJUNCT2 abi_type_dynamic_joint)) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  `EXISTS (is_abi_dynamic (make_struct_fields_map tops)) tys =
    EXISTS (\ty. is_dynamic (vyper_to_abi_type (type_env tops) ty)) tys` by
    (irule abi_dynamic_exists >> simp[]) >>
  `~is_abi_dynamic cenv.ce_struct_fields (TupleT tys)` by
    (simp_tac bool_ss [Once is_abi_dynamic_def] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []) >>
  `EVERY type_memory_layout tys` by simp[EVERY_MEM, CONJUNCT1 all_type_memory_layouts] >>
  drule_all type_memory_layout_list >> DISCH_TAC >>
  qpat_x_assum `~is_abi_dynamic _ (TupleT tys)`
    (fn th => simp_tac bool_ss [th, Once type_to_abi_enc_info_def]) >>
  simp[type_memory_bytes_def, type_memory_size_list_sum] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source/compiler ABI type shape: " ^ name)
  end) (DB.thms "abiTypeShape")
