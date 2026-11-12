Theory extRetSemanticMembersLedgerPtr
Ancestors
  extRetSemanticLedgerProbePtr extRetRecursiveLayoutPtr extRetNumericLedgerPtr
  abiEncoderSourceAggregate abiEncoderSourceTransport abiEncoderOpenInput
  abiDecodeRanges entryDecodePlanProps abiDecoderMembers abiEncoderInput vyperTypeABI
  vyperABI vyperTyping vyperValue valueEncoding contractABI retAbiPlanProps
  vyperTypeValues vyperTypeDefaults stmtSimForArray list rich_list arithmetic finite_map

(* The numerical layout condition is weaker than ABI cardinality typing. *)
Theorem encoder_semantic_list_layout:
  LENGTH tys = LENGTH tvs /\ LENGTH vs = LENGTH tys /\
  vyper_to_abi_list env tys vs = SOME avs /\
  (!i. i < LENGTH tys ==>
    evaluate_type env (EL i tys) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs)) ==>
  LIST_REL abi_encoder_layout_valid (vyper_to_abi_types env tys) avs
Proof
  strip_tac >> drule abi_encoder_list_conversion >> strip_tac >>
  simp[LIST_REL_EL_EQN, vyper_to_abi_types_MAP, EL_MAP,
       abi_encoder_layout_valid_def] >> rpt strip_tac >>
  rename1 `n < LENGTH tvs` >>
  `n < LENGTH tys` by simp[] >>
  qpat_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
    (qspec_then `n` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `vyper_to_abi env (EL n tys) (EL n vs) = SOME (EL n avs)` by simp[] >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >>
  drule_all (cj 1 static_length_memory_size) >> simp[]
QED

Theorem encoder_semantic_list_length_ledger:
  LENGTH tys = LENGTH tvs /\ LENGTH vs = LENGTH tys /\
  vyper_to_abi_list env tys vs = SOME avs /\
  (!i. i < LENGTH tys ==>
    evaluate_type env (EL i tys) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs)) ==>
  ?ats ns hs ts.
    ats = vyper_to_abi_types env tys /\
    ns = MAP2 (\at av. LENGTH (enc at av)) ats avs /\
    hs = MAP abi_member_head_size ats /\
    ts = MAP2 abi_member_tail_size ats avs /\
    LENGTH ats = LENGTH tys /\ LENGTH avs = LENGTH tys /\
    LENGTH ns = LENGTH tys /\ LENGTH hs = LENGTH tys /\ LENGTH ts = LENGTH tys /\
    (!i. i < LENGTH tys ==>
      vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs) /\
      EL i ats = vyper_to_abi_type env (EL i tys) /\
      EL i ns = LENGTH (enc (EL i ats) (EL i avs)) /\
      EL i hs = (if is_dynamic (EL i ats) then 32 else static_length (EL i ats)) /\
      EL i ts = (if is_dynamic (EL i ats) then EL i ns else 0) /\
      EL i ns <= vyper_abi_size_bound env (EL i tys)) /\
    LENGTH (enc (Tuple ats) (ListV avs)) = SUM hs + SUM ts
Proof
  strip_tac >> drule_all encoder_semantic_list_layout >> strip_tac >>
  drule abi_encoder_list_conversion >> strip_tac >>
  qexistsl [`vyper_to_abi_types env tys`,
    `MAP2 (\at av. LENGTH (enc at av)) (vyper_to_abi_types env tys) avs`,
    `MAP abi_member_head_size (vyper_to_abi_types env tys)`,
    `MAP2 abi_member_tail_size (vyper_to_abi_types env tys) avs`] >>
  simp[vyper_to_abi_types_MAP, LENGTH_MAP2] >> conj_tac
  >- (rpt strip_tac >> simp[EL_MAP2, EL_MAP, abi_member_head_size_def,
                           abi_member_tail_size_def] >>
      irule (cj 1 vyper_to_abi_enc_length_bound) >>
      qexistsl [`EL i tvs`, `EL i vs`] >> simp[]) >>
  fs[vyper_to_abi_types_MAP] >>
  drule abi_encoder_open_enc_tuple_length >> simp[]
QED

Theorem encoder_semantic_tuple_length_ledger:
  evaluate_type env (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) ==>
  ?avs.
    vyper_to_abi_list env tys vs = SOME avs /\
    vyper_to_abi env (TupleT tys) (ArrayV (TupleV vs)) = SOME (ListV avs) /\
    LENGTH avs = LENGTH tys /\ LENGTH vs = LENGTH tys /\ LENGTH tvs = LENGTH tys /\
    LIST_REL abi_encoder_layout_valid (vyper_to_abi_types env tys) avs /\
    (!i. i < LENGTH tys ==>
      evaluate_type env (EL i tys) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i vs) /\
      vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs) /\
      LENGTH (enc (vyper_to_abi_type env (EL i tys)) (EL i avs)) <=
        vyper_abi_size_bound env (EL i tys)) /\
    LENGTH (enc (vyper_to_abi_type env (TupleT tys)) (ListV avs)) =
      SUM (MAP abi_member_head_size (vyper_to_abi_types env tys)) +
      SUM (MAP2 abi_member_tail_size (vyper_to_abi_types env tys) avs)
Proof
  strip_tac >>
  `evaluate_types env tys [] = SOME tvs` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> simp[LIST_REL_EL_EQN] >> strip_tac >>
  `values_have_types tvs vs` by fs[value_has_type_def] >>
  `LENGTH vs = LENGTH tys` by metis_tac[values_have_types_length] >>
  `!i. i < LENGTH tys ==> value_has_type (EL i tvs) (EL i vs)` by
    fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid (vyper_to_abi_types env tys) avs` by
    (irule encoder_semantic_list_layout >> qexistsl [`tvs`, `vs`] >> simp[]) >>
  drule abi_encoder_list_conversion >> strip_tac >>
  qexists `avs` >> fs[Excl "enc_def", vyper_to_abi_types_MAP, LIST_REL_EL_EQN] >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 vyper_to_abi_enc_length_bound) >>
      qexistsl [`EL i tvs`, `EL i vs`] >> simp[]) >>
  `LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs` by
    simp[LIST_REL_EL_EQN] >>
  drule abi_encoder_open_enc_tuple_length >> simp[]
QED

Theorem encoder_semantic_struct_length_ledger:
  evaluate_type env (StructT nsid) = SOME (StructTV fts) /\
  value_has_type (StructTV fts) (StructV fields) ==>
  ?args tvs avs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    fts = ZIP (MAP FST args,tvs) /\
    vyper_to_abi_list (env \\ nsid) (MAP SND args) (MAP SND fields) = SOME avs /\
    vyper_to_abi env (StructT nsid) (StructV fields) = SOME (ListV avs) /\
    LENGTH avs = LENGTH args /\ LENGTH fields = LENGTH args /\ LENGTH tvs = LENGTH args /\
    LIST_REL abi_encoder_layout_valid (vyper_to_abi_types (env \\ nsid) (MAP SND args)) avs /\
    (!i. i < LENGTH args ==>
      evaluate_type (env \\ nsid) (EL i (MAP SND args)) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i (MAP SND fields)) /\
      vyper_to_abi (env \\ nsid) (EL i (MAP SND args)) (EL i (MAP SND fields)) =
        SOME (EL i avs) /\
      LENGTH (enc (vyper_to_abi_type (env \\ nsid) (EL i (MAP SND args))) (EL i avs)) <=
        vyper_abi_size_bound (env \\ nsid) (EL i (MAP SND args))) /\
    LENGTH (enc (vyper_to_abi_type env (StructT nsid)) (ListV avs)) =
      SUM (MAP abi_member_head_size (vyper_to_abi_types (env \\ nsid) (MAP SND args))) +
      SUM (MAP2 abi_member_tail_size (vyper_to_abi_types (env \\ nsid) (MAP SND args)) avs)
Proof
  strip_tac >>
  `?args tvs. FLOOKUP env nsid = SOME (StructArgs args) /\
     evaluate_types (env \\ nsid) (MAP SND args) [] = SOME tvs /\
     fts = ZIP (MAP FST args,tvs)` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> simp[LIST_REL_EL_EQN] >> strip_tac >>
  `MAP SND fts = tvs /\ LENGTH fts = LENGTH args` by simp[MAP_ZIP, LENGTH_ZIP] >>
  `values_have_types tvs (MAP SND fields)` by
    (fs[value_has_type_def] >> drule struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
  `LENGTH fields = LENGTH args` by
    (drule values_have_types_length >> simp[]) >>
  `!i. i < LENGTH args ==> value_has_type (EL i tvs) (EL i (MAP SND fields))` by
    fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid
     (vyper_to_abi_types (env \\ nsid) (MAP SND args)) avs` by
    (irule encoder_semantic_list_layout >>
     qexistsl [`tvs`, `MAP SND fields`] >> simp[]) >>
  drule abi_encoder_list_conversion >> strip_tac >>
  qexistsl [`tvs`, `avs`] >>
  fs[Excl "enc_def", vyper_to_abi_types_MAP, LIST_REL_EL_EQN] >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 vyper_to_abi_enc_length_bound) >>
      qexistsl [`EL i tvs`, `EL i (MAP SND fields)`] >> simp[]) >>
  `LIST_REL abi_encoder_layout_valid
     (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) avs` by
    simp[LIST_REL_EL_EQN] >>
  drule abi_encoder_open_enc_tuple_length >> simp[]
QED

(* Fixed arrays use the semantic default-filled elements of sparse storage. *)
Theorem encoder_semantic_fixed_length_ledger:
  evaluate_type env (ArrayT ty (Fixed n)) = SOME (ArrayTV tv (Fixed n)) /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) ==>
  ?avs.
    vyper_to_abi env (ArrayT ty (Fixed n)) (ArrayV (SArrayV kvs)) = SOME (ListV avs) /\
    LENGTH avs = n /\
    LIST_REL abi_encoder_layout_valid (REPLICATE n (vyper_to_abi_type env ty)) avs /\
    (!i. i < n ==>
      value_has_type tv (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))) /\
      vyper_to_abi env ty (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))) =
        SOME (EL i avs) /\
      LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= vyper_abi_size_bound env ty) /\
    LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) (ListV avs)) =
      SUM (MAP abi_member_head_size (REPLICATE n (vyper_to_abi_type env ty))) +
      SUM (MAP2 abi_member_tail_size (REPLICATE n (vyper_to_abi_type env ty)) avs)
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    gvs[Once evaluate_type_def, AllCaseEqs()] >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  `?avs. av = ListV avs /\ vyper_to_abi_sparse env ty tv n kvs = SOME avs` by
    gvs[Once vyper_to_abi_def, AllCaseEqs()] >> gvs[] >>
  drule_all abi_encoder_sparse_conversion >> strip_tac >>
  `well_formed_type_value (ArrayTV tv (Fixed n))` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `!i. i < n ==> value_has_type tv
     (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))` by
    metis_tac[fixed_array_elements_typed] >>
  `LIST_REL abi_encoder_layout_valid (REPLICATE n (vyper_to_abi_type env ty)) avs` by
    (simp[LIST_REL_EL_EQN, EL_REPLICATE, abi_encoder_layout_valid_def] >>
     rpt strip_tac >>
     drule_all (cj 1 static_length_memory_size) >> strip_tac >>
     metis_tac[cj 1 vyper_to_abi_static_enc_length]) >>
  simp[Excl "enc_def"] >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 vyper_to_abi_enc_length_bound) >>
      qexistsl [`tv`, `EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs))`] >> simp[]) >>
  drule abi_encoder_open_enc_tuple_length >> simp[]
QED

(* A single metadata interface applies to tuple members and to struct
   members in the reduced environment, without identifying environments. *)
Theorem encoder_semantic_members_metadata:
  env SUBMAP tenv /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) /\
  LENGTH tys = LENGTH tvs /\
  (!i. i < LENGTH tys ==> evaluate_type env (EL i tys) = SOME (EL i tvs)) ==>
  !i. i < LENGTH tys ==>
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    abi_embedded_static_size cenv.ce_struct_fields (EL i tys) =
      abi_member_head_size (EL i (vyper_to_abi_types env tys)) /\
    is_abi_dynamic cenv.ce_struct_fields (EL i tys) =
      is_dynamic (EL i (vyper_to_abi_types env tys))
Proof
  rpt strip_tac >>
  `evaluate_type env (EL i tys) = SOME (EL i tvs)` by simp[] >>
  drule_all abi_elem_props >> simp[abi_member_head_size_def,
    vyper_to_abi_types_MAP, EL_MAP]
QED

Theorem encoder_semantic_members_ranges:
  LIST_REL abi_encoder_layout_valid ats avs /\ i < LENGTH ats ==>
  SUM (MAP abi_member_head_size (TAKE i ats)) +
    abi_member_head_size (EL i ats) <= LENGTH (enc (Tuple ats) (ListV avs)) /\
  (is_dynamic (EL i ats) ==>
    SUM (MAP abi_member_head_size ats) +
      SUM (TAKE i (MAP2 abi_member_tail_size ats avs)) +
      LENGTH (enc (EL i ats) (EL i avs)) <= LENGTH (enc (Tuple ats) (ListV avs))) /\
  (~is_dynamic (EL i ats) ==>
    SUM (MAP abi_member_head_size (TAKE i ats)) +
      LENGTH (enc (EL i ats) (EL i avs)) <= LENGTH (enc (Tuple ats) (ListV avs)))
Proof
  strip_tac >>
  `LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (enc (Tuple ats) (ListV avs)) =
    SUM (MAP abi_member_head_size ats) + SUM (MAP2 abi_member_tail_size ats avs)` by
    metis_tac[abi_encoder_open_tuple_length] >>
  `SUM (MAP abi_member_head_size (TAKE i ats)) + abi_member_head_size (EL i ats) <=
    SUM (MAP abi_member_head_size ats)` by
    (drule abi_encoder_prefix_sum_bound >>
     disch_then (qspec_then `abi_member_head_size` mp_tac) >> simp[]) >>
  `SUM (TAKE i (MAP2 abi_member_tail_size ats avs)) +
     EL i (MAP2 abi_member_tail_size ats avs) <= SUM (MAP2 abi_member_tail_size ats avs)` by
    (qspecl_then [`I`, `MAP2 abi_member_tail_size ats avs`, `i`]
       mp_tac abi_encoder_prefix_sum_bound >> simp[LENGTH_MAP2, MAP_ID]) >>
  `abi_encoder_layout_valid (EL i ats) (EL i avs)` by
    fs[LIST_REL_EL_EQN] >>
  fs[EL_MAP2, abi_member_tail_size_def, abi_member_head_size_def,
     abi_encoder_layout_valid_def] >>
  Cases_on `is_dynamic (EL i ats)` >>
  gvs[EL_MAP2, abi_member_tail_size_def]
QED
