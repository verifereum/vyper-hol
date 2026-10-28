(* TOP-LEVEL: compiler ABI head widths agree with source ABI widths for
   every evaluated type, including recursive aggregates and named structs.
   Helpers compose static fields under the corresponding struct guards. *)
Theory abiTypeWidths
Ancestors
  abiTypeShape sourceAbiStaticWidth typeLayoutProps structSourceProps
  sourceAbiTypingLists compileEnv valueEncoding vyperABI vyperValue vyperAST
  vyperTypeABI vyperTypeValues contractABI finite_map list pair combin arithmetic

Theorem abi_base_embedded_width:
  !sfields bt.
    abi_embedded_static_size sfields (BaseT bt) =
      if is_dynamic (vyper_base_to_abi_type bt) then 32 else static_length (vyper_base_to_abi_type bt)
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
    vyper_base_to_abi_type_def, is_dynamic_def, static_length_def] >>
  qmatch_goalsub_rename_tac `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def,
    vyper_base_to_abi_type_def, is_dynamic_def, static_length_def]
QED

Theorem abi_static_tuple_width:
  !sfields tys.
    abi_static_size sfields (TupleT tys) = SUM (MAP (abi_embedded_static_size sfields) tys)
Proof
  rpt gen_tac >> simp_tac bool_ss [Once abi_static_size_def, GSYM abi_embedded_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem abi_static_embedded_lengths:
  !tys tenv sfields.
    EVERY (\ty. abi_embedded_static_size sfields ty =
      if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) tys /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys ==>
    SUM (MAP (abi_embedded_static_size sfields) tys) =
      static_length (Tuple (MAP (vyper_to_abi_type tenv) tys))
Proof
  Induct_on `tys` >> simp[static_length_Tuple_SUM] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`tenv`, `sfields`] mp_tac) >> simp[static_length_Tuple_SUM]
QED

Theorem abi_embedded_tuple_case:
  !tenv tys.
    (!sfields tvs. abi_struct_env_rel tenv sfields /\
      LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
      EVERY (\ty. abi_embedded_static_size sfields ty =
        if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) tys) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (TupleT tys) = SOME tv ==>
      abi_embedded_static_size sfields (TupleT tys) =
        if is_dynamic (vyper_to_abi_type tenv (TupleT tys)) then 32
        else static_length (vyper_to_abi_type tenv (TupleT tys))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `TupleT tys`, `sfields`, `tv`] (CONJUNCT1 abi_type_dynamic_joint)) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  Cases_on `is_dynamic (vyper_to_abi_type tenv (TupleT tys))`
  >- simp[abi_embedded_static_size_def] >>
  drule evaluate_type_TupleT_cases >> strip_tac >> first_x_assum drule_all >> DISCH_TAC >>
  `~EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys` by
    fs[Once vyper_to_abi_type_def, is_dynamic_def, any_dynamic_EXISTS, source_abi_types_map, EXISTS_MAP] >>
  drule_all abi_static_embedded_lengths >> DISCH_TAC >>
  `abi_static_size sfields (TupleT tys) = SUM (MAP (abi_embedded_static_size sfields) tys)` by
    MATCH_ACCEPT_TAC abi_static_tuple_width >>
  asm_simp_tac bool_ss [abi_embedded_static_size_def] >>
  simp[Once vyper_to_abi_type_def, source_abi_types_map]
QED

Theorem abi_embedded_fixed_array_case:
  !tenv elem num_elems.
    (!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv elem = SOME tv ==>
      abi_embedded_static_size sfields elem =
        if is_dynamic (vyper_to_abi_type tenv elem) then 32 else static_length (vyper_to_abi_type tenv elem)) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (ArrayT elem (Fixed num_elems)) = SOME tv ==>
      abi_embedded_static_size sfields (ArrayT elem (Fixed num_elems)) =
        if is_dynamic (vyper_to_abi_type tenv (ArrayT elem (Fixed num_elems))) then 32
        else static_length (vyper_to_abi_type tenv (ArrayT elem (Fixed num_elems)))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> rename1 `evaluate_type tenv elem = SOME elem_tv` >>
  first_x_assum drule_all >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `elem`, `sfields`, `elem_tv`] (CONJUNCT1 abi_type_dynamic_joint)) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `abi_static_size sfields (ArrayT elem (Fixed num_elems)) =
    num_elems * abi_embedded_static_size sfields elem` by
    simp_tac bool_ss [Once abi_static_size_def, GSYM abi_embedded_static_size_def] >>
  asm_simp_tac (srw_ss()) [abi_embedded_static_size_def, Once is_abi_dynamic_def,
    Once vyper_to_abi_type_def, is_dynamic_def, static_length_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type tenv elem)` >> fs[abi_embedded_static_size_def]
QED

Theorem abi_static_struct_width:
  !sfields nsid fields.
    FLOOKUP sfields (nsid_to_string nsid) = SOME fields ==>
    abi_static_size sfields (StructT nsid) =
      SUM (MAP (abi_embedded_static_size (sfields \\ nsid_to_string nsid)) (MAP (FST o SND) fields))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [Once abi_static_size_def, LET_THM] >>
  asm_simp_tac (srw_ss()) [GSYM abi_embedded_static_size_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem abi_embedded_struct_case:
  !tenv nsid.
    (!arg_kind args. FLOOKUP tenv nsid = SOME arg_kind /\ arg_kind = StructArgs args ==>
      !sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\
        LIST_REL (\ty tv. evaluate_type (tenv \\ nsid) ty = SOME tv) (MAP SND args) tvs ==>
        EVERY (\ty. abi_embedded_static_size sfields ty =
          if is_dynamic (vyper_to_abi_type (tenv \\ nsid) ty) then 32
          else static_length (vyper_to_abi_type (tenv \\ nsid) ty)) (MAP SND args)) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (StructT nsid) = SOME tv ==>
      abi_embedded_static_size sfields (StructT nsid) =
        if is_dynamic (vyper_to_abi_type tenv (StructT nsid)) then 32
        else static_length (vyper_to_abi_type tenv (StructT nsid))
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `StructT nsid`, `sfields`, `tv`] (CONJUNCT1 abi_type_dynamic_joint)) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  Cases_on `is_dynamic (vyper_to_abi_type tenv (StructT nsid))`
  >- simp[abi_embedded_static_size_def] >>
  qpat_x_assum `!arg_kind args. _` (fn ih =>
    qpat_x_assum `evaluate_type _ _ = _` (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
    strip_tac >> gvs[AllCaseEqs()] >> ASSUME_TAC ih) >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs source_args)` >>
  rename1 `evaluate_types (tenv \\ nsid) (MAP SND source_args) [] = SOME field_tvs` >>
  drule_all abi_struct_env_rel_lookup >> strip_tac >> drule_all abi_struct_env_rel_domsub >> DISCH_TAC >>
  drule evaluate_types_LIST_REL >> DISCH_TAC >>
  qpat_x_assum `!arg_kind args. _`
    (qspecl_then [`StructArgs source_args`, `source_args`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `!sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\ _ ==> _`
    (qspecl_then [`sfields \\ nsid_to_string nsid`, `field_tvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `~EXISTS (\ty. is_dynamic (vyper_to_abi_type (tenv \\ nsid) ty)) (MAP SND source_args)` by
    fs[any_dynamic_EXISTS, source_abi_types_map, EXISTS_MAP, EVERY_MAP, o_DEF] >>
  drule_all abi_static_embedded_lengths >> DISCH_TAC >>
  `abi_static_size sfields (StructT nsid) =
    SUM (MAP (abi_embedded_static_size (sfields \\ nsid_to_string nsid)) (MAP SND source_args))` by
    (qpat_assum `MAP (FST o SND) fields = MAP SND source_args`
       (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     irule abi_static_struct_width >> first_assum MATCH_ACCEPT_TAC) >>
  asm_simp_tac bool_ss [abi_embedded_static_size_def] >>
  simp[Once vyper_to_abi_type_def, source_abi_types_map]
QED

Theorem abi_embedded_cons_case:
  !tenv ty tys.
    ((!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
       abi_embedded_static_size sfields ty =
         if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) /\
     (!sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
       EVERY (\ty. abi_embedded_static_size sfields ty =
         if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) tys)) ==>
    !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (ty::tys) tvs ==>
      EVERY (\ty. abi_embedded_static_size sfields ty =
        if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) (ty::tys)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_type_embedded_width_joint:
  (!tenv ty. !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
    abi_embedded_static_size sfields ty =
      if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) /\
  (!tenv tys. !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    EVERY (\ty. abi_embedded_static_size sfields ty =
      if is_dynamic (vyper_to_abi_type tenv ty) then 32 else static_length (vyper_to_abi_type tenv ty)) tys)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac >|
    [simp[abi_base_embedded_width],
     MATCH_ACCEPT_TAC abi_embedded_tuple_case,
     simp[abi_embedded_static_size_def, Once is_abi_dynamic_def, Once vyper_to_abi_type_def, is_dynamic_def],
     MATCH_ACCEPT_TAC abi_embedded_fixed_array_case,
     MATCH_ACCEPT_TAC abi_embedded_struct_case,
     simp[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def, is_dynamic_def, static_length_def],
     simp[abi_embedded_static_size_def, is_abi_dynamic_def, abi_static_size_def, is_dynamic_def, static_length_def],
     simp[],
     MATCH_ACCEPT_TAC abi_embedded_cons_case]
QED

Theorem evaluated_abi_embedded_width:
  !tenv sfields ty tv.
    abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
    abi_embedded_static_size sfields ty =
      if is_dynamic (vyper_to_abi_type tenv ty) then 32 else type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (CONJUNCT1 abi_type_embedded_width_joint) >> DISCH_TAC >>
  Cases_on `is_dynamic (vyper_to_abi_type tenv ty)` >- simp[] >>
  drule_all (CONJUNCT1 source_abi_static_width) >> simp[]
QED

Theorem evaluated_static_embedded_list_width:
  !tys tvs tenv sfields.
    abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type tenv ty)) tys ==>
    SUM (MAP (abi_embedded_static_size sfields) tys) = type_memory_size_list tvs
Proof
  Induct_on `tys` >- (Cases_on `tvs` >> simp[type_memory_size_def]) >>
  qx_gen_tac `ty` >> rpt gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  rename1 `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tail_tvs` >>
  drule_all evaluated_abi_embedded_width >> DISCH_TAC >>
  first_x_assum (qspecl_then [`tail_tvs`, `tenv`, `sfields`] mp_tac) >> simp[type_memory_size_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source/compiler ABI widths: " ^ name)
  end) (DB.thms "abiTypeWidths")
