Theory entryNormalizedBackwardExists
Ancestors
  abiValueEncoding entryAbiMemoryTransport entryValueMemoryCongruence abiEncoderSourceTransport rich_list vyperABIRoundtrip
  vyperABI vyperTyping vyperTypeDefaults vyperTypeValues vyperValue contractABI words list
Libs intLib

Theorem entry_base_backward_exists[local]:
  value_has_type (BaseTV bt) v /\ vyper_to_abi_base bt v = SOME av ==>
  ?nv. abi_to_vyper env (BaseT bt) av = SOME nv
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[value_has_type_def, vyper_to_abi_base_def] >> rpt strip_tac >> gvs[] >>
  simp[abi_to_vyper_def, check_IntV_def]
  >- simp[within_int_bound_def]
  >- (Cases_on `b` >> simp[])
  >- (Cases_on `b` >> gvs[value_has_type_def, compatible_bound_def]) >>
  mp_tac (Q.ISPEC `word_of_bytes_be l : address` w2n_lt) >>
  simp[within_int_bound_def, dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``]
QED

Theorem entry_backward_list_exists[local]:
  !ts avs. LENGTH ts = LENGTH avs /\
    (!i. i < LENGTH avs ==> ?nv. abi_to_vyper env (EL i ts) (EL i avs) = SOME nv) ==>
    ?nvs. abi_to_vyper_list env ts avs = SOME nvs
Proof
  Induct >> Cases_on `avs` >> simp[abi_to_vyper_def] >> rpt strip_tac >>
  qpat_assum `!i. i < SUC _ ==> _`
    (qspec_then `0` (strip_assume_tac o SRULE [])) >>
  `?nvs. abi_to_vyper_list env ts t = SOME nvs` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem entry_abi_child_size[local]:
  !avs i. i < LENGTH avs ==> abi_value_size (EL i avs) < list_size abi_value_size avs + 1
Proof
  Induct >> Cases_on `i` >> simp[abi_value_size_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[abi_value_size_def] >> decide_tac
QED

Theorem entry_tuple_backward_exists[local]:
  (!av' env ty tv v. abi_value_size av' < abi_value_size av /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av' ==> ?nv. abi_to_vyper env ty av' = SOME nv) /\
  evaluate_type env (TupleT ts) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (TupleT ts) v = SOME av ==>
  ?nv. abi_to_vyper env (TupleT ts) av = SOME nv
Proof
  strip_tac >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule abi_encoder_list_conversion >> strip_tac >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `?nvs. abi_to_vyper_list env ts avs = SOME nvs` by
    (irule entry_backward_list_exists >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> conj_tac
     >- (irule entry_abi_child_size >> simp[]) >>
     qexistsl [`EL i tvs`, `EL i l`] >> simp[]) >>
  simp[Once abi_to_vyper_def]
QED

Theorem entry_array_backward_exists[local]:
  (!av' env ty tv v. abi_value_size av' < abi_value_size av /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av' ==> ?nv. abi_to_vyper env ty av' = SOME nv) /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (ArrayT ty bd) v = SOME av ==>
  ?nv. abi_to_vyper env (ArrayT ty bd) av = SOME nv
Proof
  strip_tac >> drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> Cases_on `bd` >>
  gvs[value_has_type_def, Once vyper_to_abi_def, AllCaseEqs()]
  >- (drule abi_encoder_same_conversion >> strip_tac >>
      gvs[all_have_type_EVERY, EVERY_EL] >>
      `?nvs. abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME nvs` by
        (irule entry_backward_list_exists >> simp[] >> rpt strip_tac >>
         simp[EL_REPLICATE] >> first_x_assum irule >> conj_tac
         >- (irule entry_abi_child_size >> simp[]) >>
         qexistsl [`elem_tv`, `EL i l`] >> simp[]) >>
      gvs[Once abi_to_vyper_def, compatible_bound_def]) >>
  `value_has_type (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV l))` by
    simp[value_has_type_def] >>
  drule abi_encoder_sparse_conversion >> disch_then drule >> strip_tac >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  `?nvs. abi_to_vyper_list env (REPLICATE (LENGTH avs) ty) avs = SOME nvs` by
    (irule entry_backward_list_exists >> simp[] >> rpt strip_tac >>
     simp[EL_REPLICATE] >> first_x_assum irule >> conj_tac
     >- (irule entry_abi_child_size >> simp[]) >>
     qexistsl [`elem_tv`,
       `EL i (array_elements (ArrayTV elem_tv (Fixed n)) (SArrayV l))`] >>
     simp[] >> metis_tac[entry_typed_sparse_element]) >>
  gvs[Once abi_to_vyper_def, compatible_bound_def]
QED

Theorem entry_struct_backward_exists[local]:
  (!av' env ty tv v. abi_value_size av' < abi_value_size av /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av' ==> ?nv. abi_to_vyper env ty av' = SOME nv) /\
  evaluate_type env (StructT nsid) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env (StructT nsid) v = SOME av ==>
  ?nv. abi_to_vyper env (StructT nsid) av = SOME nv
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule evaluate_types_length >> simp[] >> strip_tac >>
  imp_res_tac struct_has_type_values_have_types >>
  drule vyperTypeABITheory.evaluate_types_LIST_REL >> strip_tac >>
  drule abi_encoder_list_conversion >> strip_tac >>
  gvs[MAP_ZIP, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `?nvs. abi_to_vyper_list (env \\ nsid) (MAP SND args) avs = SOME nvs` by
    (irule entry_backward_list_exists >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> conj_tac
     >- (irule entry_abi_child_size >> simp[]) >>
     qexistsl [`EL i tvs`, `EL i (MAP SND l)`] >> simp[]) >>
  simp[Once abi_to_vyper_def]
QED

Theorem entry_typed_forward_backward_exists:
  !av env ty tv v.
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==> ?nv. abi_to_vyper env ty av = SOME nv
Proof
  gen_tac >> completeInduct_on `abi_value_size av` >> rpt strip_tac >>
  Cases_on `ty`
  >- (drule evaluate_type_base_result >> strip_tac >> gvs[] >>
      gvs[Once vyper_to_abi_def] >> irule entry_base_backward_exists >> metis_tac[])
  >- (irule entry_tuple_backward_exists >> simp[] >> metis_tac[])
  >- (irule entry_array_backward_exists >> simp[] >> metis_tac[])
  >- (irule entry_struct_backward_exists >> simp[] >> metis_tac[]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >> Cases_on `v'` >>
  gvs[value_has_type_def, Once vyper_to_abi_def] >>
  simp[Once abi_to_vyper_def]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_typed_forward_backward_exists)
  in if null axioms andalso null (Thm.hyp entry_typed_forward_backward_exists) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry backward existence inherited admission"
  end;
