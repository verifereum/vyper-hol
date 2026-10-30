(* TOP-LEVEL: the compiler's complete ABI size bound equals the source
   bound for every evaluated type and tuple field list. Helpers compare
   static sizes, recursive array elements and matching struct guards. *)
Theory abiTypeBounds
Ancestors
  sourceAbiShape abiTypeShape abiTypeWidths abiStaticBounds
  sourceAbiTypingLists compileEnv valueEncoding vyperABI vyperValue vyperAST
  vyperTypeABI vyperTypeValues contractABI finite_map list pair combin arithmetic

Theorem abi_size_bound_struct_fields:
  !sfields nsid fields.
    FLOOKUP sfields (nsid_to_string nsid) = SOME fields ==>
    abi_size_bound sfields (StructT nsid) =
      SUM (MAP (\ty. abi_embedded_static_size (sfields \\ nsid_to_string nsid) ty +
        (if is_abi_dynamic (sfields \\ nsid_to_string nsid) ty
         then abi_size_bound (sfields \\ nsid_to_string nsid) ty else 0)) (MAP (FST o SND) fields))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [Once abi_size_bound_def, LET_THM] >> simp[]
QED

Theorem abi_size_bound_static_base:
  !sfields bt.
    ~is_abi_dynamic sfields (BaseT bt) ==>
    abi_size_bound sfields (BaseT bt) = abi_static_size sfields (BaseT bt)
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[Once is_abi_dynamic_def, Once abi_size_bound_def, abi_static_size_def] >>
  qmatch_goalsub_rename_tac `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[Once is_abi_dynamic_def, Once abi_size_bound_def, abi_static_size_def]
QED

Theorem abi_size_bound_static_tuple:
  !sfields tys.
    ~is_abi_dynamic sfields (TupleT tys) ==>
    abi_size_bound sfields (TupleT tys) = abi_static_size sfields (TupleT tys)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `~is_abi_dynamic sfields (TupleT tys)`
    (ASSUME_TAC o CONV_RULE (DEPTH_CONV ETA_CONV) o ONCE_REWRITE_RULE [is_abi_dynamic_def]) >>
  drule_all abi_static_tuple_bound >> simp[abi_static_tuple_width]
QED

Theorem abi_size_bound_static_struct:
  !sfields nsid.
    ~is_abi_dynamic sfields (StructT nsid) ==>
    abi_size_bound sfields (StructT nsid) = abi_static_size sfields (StructT nsid)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP sfields (nsid_to_string nsid)`
  >- simp[Once abi_size_bound_def, Once abi_static_size_def, LET_THM] >>
  rename1 `FLOOKUP sfields (nsid_to_string nsid) = SOME fields` >>
  `~EXISTS (is_abi_dynamic (sfields \\ nsid_to_string nsid)) (MAP (FST o SND) fields)` by
    (fs[Once is_abi_dynamic_def, LET_THM] >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> first_assum MATCH_ACCEPT_TAC) >>
  drule abi_size_bound_struct_fields >> DISCH_TAC >> drule abi_static_struct_width >> DISCH_TAC >>
  drule_all abi_static_tail_lengths >> simp[]
QED

Theorem abi_size_bound_static:
  !sfields ty.
    ~is_abi_dynamic sfields ty ==> abi_size_bound sfields ty = abi_static_size sfields ty
Proof
  rpt gen_tac >> Cases_on `ty` >> DISCH_TAC >|
    [drule_all abi_size_bound_static_base >> simp[],
     drule_all abi_size_bound_static_tuple >> simp[],
     rename1 `~is_abi_dynamic sfields (ArrayT elem array_bound)` >> Cases_on `array_bound` >>
       fs[Once is_abi_dynamic_def, Once abi_size_bound_def, Once abi_static_size_def, abi_embedded_static_size_def],
     drule_all abi_size_bound_static_struct >> simp[],
     simp[Once abi_size_bound_def],
     simp[Once abi_size_bound_def]]
QED

Theorem evaluated_compiler_abi_dynamic:
  !tenv sfields ty tv.
    abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
    is_abi_dynamic sfields ty = vyper_is_dynamic tenv ty
Proof
  rpt gen_tac >> strip_tac >> drule_all (CONJUNCT1 abi_type_dynamic_joint) >>
  simp[CONJUNCT1 source_abi_dynamic_shape]
QED

Theorem abi_bound_field_source:
  !tenv sfields ty tv.
    abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv /\
    abi_size_bound sfields ty = vyper_abi_size_bound tenv ty ==>
    abi_embedded_static_size sfields ty +
      (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0) = vyper_abi_embedded_size tenv ty
Proof
  rpt gen_tac >> strip_tac >> drule_all evaluated_compiler_abi_dynamic >> DISCH_TAC >>
  Cases_on `is_abi_dynamic sfields ty`
  >- fs[abi_embedded_static_size_def, Once vyper_abi_size_bound_def] >>
  drule_all abi_size_bound_static >> DISCH_TAC >>
  fs[abi_embedded_static_size_def, Once vyper_abi_size_bound_def]
QED

Theorem abi_base_size_bound:
  !tenv sfields bt.
    abi_size_bound sfields (BaseT bt) = vyper_abi_size_bound tenv (BaseT bt)
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[Once abi_size_bound_def, Once vyper_abi_size_bound_def, abi_static_size_def, ceil32_def, MULT_COMM] >>
  qmatch_goalsub_rename_tac `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[Once abi_size_bound_def, Once vyper_abi_size_bound_def, abi_static_size_def, ceil32_def, MULT_COMM]
QED

Theorem abi_bound_tuple_case:
  !tenv tys.
    (!sfields tvs. abi_struct_env_rel tenv sfields /\
      LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
      SUM (MAP (\ty. abi_embedded_static_size sfields ty +
        (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) tys) =
          vyper_abi_size_bound_list tenv tys) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (TupleT tys) = SOME tv ==>
      abi_size_bound sfields (TupleT tys) = vyper_abi_size_bound tenv (TupleT tys)
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_TupleT_cases >> strip_tac >> first_x_assum drule_all >> DISCH_TAC >>
  simp[Once abi_size_bound_def, Once vyper_abi_size_bound_def]
QED

Theorem abi_bound_array_cases:
  (!tenv elem num_elems.
    (!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv elem = SOME tv ==>
      abi_size_bound sfields elem = vyper_abi_size_bound tenv elem) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (ArrayT elem (Fixed num_elems)) = SOME tv ==>
      abi_size_bound sfields (ArrayT elem (Fixed num_elems)) = vyper_abi_size_bound tenv (ArrayT elem (Fixed num_elems))) /\
  (!tenv elem num_elems.
    (!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv elem = SOME tv ==>
      abi_size_bound sfields elem = vyper_abi_size_bound tenv elem) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (ArrayT elem (Dynamic num_elems)) = SOME tv ==>
      abi_size_bound sfields (ArrayT elem (Dynamic num_elems)) = vyper_abi_size_bound tenv (ArrayT elem (Dynamic num_elems)))
Proof
  conj_tac >> (rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> rename1 `evaluate_type tenv elem = SOME elem_tv` >>
  first_x_assum drule_all >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `sfields`, `elem`, `elem_tv`] abi_bound_field_source) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [vyper_abi_size_bound_def])) >>
  asm_simp_tac bool_ss [Once abi_size_bound_def])
QED

Theorem abi_bound_struct_case:
  !tenv nsid.
    (!arg_kind args. FLOOKUP tenv nsid = SOME arg_kind /\ arg_kind = StructArgs args ==>
      !sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\
        LIST_REL (\ty tv. evaluate_type (tenv \\ nsid) ty = SOME tv) (MAP SND args) tvs ==>
        SUM (MAP (\ty. abi_embedded_static_size sfields ty +
          (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) (MAP SND args)) =
            vyper_abi_size_bound_list (tenv \\ nsid) (MAP SND args)) ==>
    !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv (StructT nsid) = SOME tv ==>
      abi_size_bound sfields (StructT nsid) = vyper_abi_size_bound tenv (StructT nsid)
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!arg_kind args. _` (fn ih =>
    qpat_x_assum `evaluate_type _ _ = _` (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
    strip_tac >> gvs[AllCaseEqs()] >> ASSUME_TAC ih) >>
  rename1 `FLOOKUP tenv nsid = SOME (StructArgs source_args)` >>
  rename1 `evaluate_types (tenv \\ nsid) (MAP SND source_args) [] = SOME field_tvs` >>
  drule_all abi_struct_env_rel_lookup >> strip_tac >> drule_all abi_struct_env_rel_domsub >> DISCH_TAC >>
  drule evaluate_types_LIST_REL >> DISCH_TAC >>
  qpat_x_assum `!arg_kind args. _` (qspecl_then [`StructArgs source_args`, `source_args`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `!sfields tvs. abi_struct_env_rel (tenv \\ nsid) sfields /\ _ ==> _`
    (qspecl_then [`sfields \\ nsid_to_string nsid`, `field_tvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule abi_size_bound_struct_fields >> DISCH_TAC >>
  qpat_assum `MAP (FST o SND) fields = MAP SND source_args` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  simp[Once vyper_abi_size_bound_def]
QED

Theorem abi_bound_cons_case:
  !tenv ty tys.
    ((!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
       abi_size_bound sfields ty = vyper_abi_size_bound tenv ty) /\
     (!sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
       SUM (MAP (\ty. abi_embedded_static_size sfields ty +
         (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) tys) =
           vyper_abi_size_bound_list tenv tys)) ==>
    !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (ty::tys) tvs ==>
      SUM (MAP (\ty. abi_embedded_static_size sfields ty +
        (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) (ty::tys)) =
          vyper_abi_size_bound_list tenv (ty::tys)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `tvs` >> simp[] >> strip_tac >>
  rename1 `evaluate_type tenv ty = SOME field_tv` >>
  rename1 `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tail_tvs` >>
  qpat_x_assum `!sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==> _`
    (qspecl_then [`sfields`, `field_tv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `sfields`, `ty`, `field_tv`] abi_bound_field_source) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qpat_x_assum `!sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL _ tys tvs ==> _`
    (qspecl_then [`sfields`, `tail_tvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [vyper_abi_size_bound_def])) >>
  qpat_assum `abi_embedded_static_size sfields ty + _ = vyper_abi_embedded_size tenv ty`
    (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `SUM (MAP _ tys) = vyper_abi_size_bound_list tenv tys` (fn th => PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_size_bound sfields ty = vyper_abi_size_bound tenv ty` (fn th => PURE_REWRITE_TAC [th]) >>
  CONV_TAC (AC_CONV (ADD_ASSOC, ADD_COMM))
QED

Theorem abi_type_size_bound_joint:
  (!tenv ty. !sfields tv. abi_struct_env_rel tenv sfields /\ evaluate_type tenv ty = SOME tv ==>
    abi_size_bound sfields ty = vyper_abi_size_bound tenv ty) /\
  (!tenv tys. !sfields tvs. abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    SUM (MAP (\ty. abi_embedded_static_size sfields ty +
      (if is_abi_dynamic sfields ty then abi_size_bound sfields ty else 0)) tys) = vyper_abi_size_bound_list tenv tys)
Proof
  ho_match_mp_tac vyper_to_abi_type_ind >> rpt conj_tac >|
    [simp[abi_base_size_bound],
     MATCH_ACCEPT_TAC abi_bound_tuple_case,
     MATCH_ACCEPT_TAC (CONJUNCT2 abi_bound_array_cases),
     MATCH_ACCEPT_TAC (CONJUNCT1 abi_bound_array_cases),
     MATCH_ACCEPT_TAC abi_bound_struct_case,
     simp[Once abi_size_bound_def, Once vyper_abi_size_bound_def, abi_static_size_def],
     simp[Once abi_size_bound_def, Once vyper_abi_size_bound_def, abi_static_size_def],
     simp[Once vyper_abi_size_bound_def],
     MATCH_ACCEPT_TAC abi_bound_cons_case]
QED

Theorem evaluated_abi_tuple_size_bound:
  !tenv sfields tys tvs.
    abi_struct_env_rel tenv sfields /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    abi_size_bound sfields (TupleT tys) = vyper_abi_size_bound_list tenv tys
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [Once abi_size_bound_def] >>
  drule_all (CONJUNCT2 abi_type_size_bound_joint) >> simp[]
QED
