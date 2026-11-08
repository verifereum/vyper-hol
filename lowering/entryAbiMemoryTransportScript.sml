(* Typed common ABI conversions preserve the memory interpretation. *)
Theory entryAbiMemoryTransport
Ancestors
  entryValueMemoryCongruence abiEncoderSourceTransport abiValueEncoding vyperABI
  valueEncoding vyperValue vyperTyping vyperTypeDefaults vyperTypeValues vyperValueOperation words list venomMemProps
Libs intLib

Theorem entry_base_common_conversion_memory[local]:
  value_has_type (BaseTV bt) v /\ value_has_type (BaseTV bt) w /\
  vyper_to_abi_base bt v = SOME av /\ vyper_to_abi_base bt w = SOME av ==>
  (val_in_memory (BaseTV bt) v p mem <=> val_in_memory (BaseTV bt) w p mem)
Proof
  Cases_on `bt` >> Cases_on `v` >> Cases_on `w` >>
  simp[value_has_type_def, vyper_to_abi_base_def, val_in_memory_def] >>
  rpt strip_tac >> gvs[]
  >- (`i = i'` by intLib.ARITH_TAC >> simp[])
  >- (Cases_on `b` >> Cases_on `b'` >> gvs[])
  >- (qpat_assum `MAP _ s' = MAP _ s` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
      simp[] >> strip_tac >> gvs[vyperMiscTheory.n2w_o_ORD_eq]) >>
  gvs[typed_val_to_w256_def, val_to_w256_def] >>
  `word_of_bytes_be (PAD_LEFT 0w 32 l) =
     (w2w (word_of_bytes_be l : address):256 word)` by
    (mp_tac (INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]
       w2w_word_of_bytes_be_pad_left) >>
     simp[dividesTheory.divides_def, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
     metis_tac[]) >>
  `word_of_bytes_be (PAD_LEFT 0w 32 l') =
     (w2w (word_of_bytes_be l' : address):256 word)` by
    (mp_tac (INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]
       w2w_word_of_bytes_be_pad_left) >>
     simp[dividesTheory.divides_def, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
     metis_tac[]) >>
  asm_rewrite_tac[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_base_common_conversion_memory)
  in if null axioms andalso null (Thm.hyp entry_base_common_conversion_memory) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry primitive conversion inherited admission"
  end;

Theorem entry_tuple_common_conversion_memory[local]:
  (!tv' env ty v w av p mem.
    type_value_size tv' < type_value_size tv /\
    evaluate_type env ty = SOME tv' /\ value_has_type tv' v /\
    value_has_type tv' w /\ vyper_to_abi env ty v = SOME av /\
    vyper_to_abi env ty w = SOME av ==>
    (val_in_memory tv' v p mem <=> val_in_memory tv' w p mem)) /\
  evaluate_type env (TupleT ts) = SOME tv /\
  value_has_type tv v /\ value_has_type tv w /\
  vyper_to_abi env (TupleT ts) v = SOME av /\
  vyper_to_abi env (TupleT ts) w = SOME av ==>
  (val_in_memory tv v p mem <=> val_in_memory tv w p mem)
Proof
  strip_tac >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> Cases_on `w` >>
  gvs[value_has_type_def] >>
  Cases_on `a` >> Cases_on `a'` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  imp_res_tac abi_encoder_list_conversion >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[val_in_memory_def] >> irule entry_tuple_memory_congruence >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  conj_tac
  >- (mp_tac (Q.SPEC `tvs` MEM_type_value_size_TupleTV) >>
      simp[type_value_size_def] >> metis_tac[MEM_EL]) >>
  conj_tac >- (qexistsl [`EL i avs`, `env`, `EL i ts`] >> simp[]) >>
  simp[]
QED

Theorem entry_array_common_conversion_memory[local]:
  (!tv' env ty v w av p mem.
    type_value_size tv' < type_value_size tv /\
    evaluate_type env ty = SOME tv' /\ value_has_type tv' v /\
    value_has_type tv' w /\ vyper_to_abi env ty v = SOME av /\
    vyper_to_abi env ty w = SOME av ==>
    (val_in_memory tv' v p mem <=> val_in_memory tv' w p mem)) /\
  evaluate_type env (ArrayT ty bd) = SOME tv /\
  value_has_type tv v /\ value_has_type tv w /\
  vyper_to_abi env (ArrayT ty bd) v = SOME av /\
  vyper_to_abi env (ArrayT ty bd) w = SOME av ==>
  (val_in_memory tv v p mem <=> val_in_memory tv w p mem)
Proof
  strip_tac >> drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> Cases_on `w` >> gvs[value_has_type_def] >>
  Cases_on `a` >> Cases_on `a'` >> Cases_on `bd` >>
  gvs[value_has_type_def, Once vyper_to_abi_def, AllCaseEqs()]
  >- (imp_res_tac abi_encoder_same_conversion >>
      gvs[all_have_type_EVERY, EVERY_EL] >>
      simp[val_in_memory_def] >>
      `!p mem. elems_in_memory l p elem_tv mem <=> elems_in_memory l' p elem_tv mem` by
        (irule entry_elems_memory_congruence >> simp[LIST_REL_EL_EQN] >>
         rpt strip_tac >> first_x_assum irule >>
         simp[] >> qexistsl [`EL n' avs`, `env`, `ty`] >> simp[]) >>
      simp[]) >>
  `value_has_type (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV l)) /\
   value_has_type (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV l'))` by
    simp[value_has_type_def] >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  imp_res_tac abi_encoder_sparse_conversion >>
  asm_simp_tac bool_ss [entry_typed_sparse_memory_indexed] >>
  `!i p mem. i < n ==>
     (val_in_memory elem_tv
       (EL i (array_elements (ArrayTV elem_tv (Fixed n)) (SArrayV l))) p mem <=>
      val_in_memory elem_tv
       (EL i (array_elements (ArrayTV elem_tv (Fixed n)) (SArrayV l'))) p mem)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     conj_tac >- (qexistsl [`EL i avs`, `env`, `ty`] >> simp[]) >>
     metis_tac[entry_typed_sparse_element]) >>
  simp[]
QED

Theorem entry_struct_common_conversion_memory[local]:
  (!tv' env ty v w av p mem.
    type_value_size tv' < type_value_size tv /\
    evaluate_type env ty = SOME tv' /\ value_has_type tv' v /\
    value_has_type tv' w /\ vyper_to_abi env ty v = SOME av /\
    vyper_to_abi env ty w = SOME av ==>
    (val_in_memory tv' v p mem <=> val_in_memory tv' w p mem)) /\
  evaluate_type env (StructT nsid) = SOME tv /\
  value_has_type tv v /\ value_has_type tv w /\
  vyper_to_abi env (StructT nsid) v = SOME av /\
  vyper_to_abi env (StructT nsid) w = SOME av ==>
  (val_in_memory tv v p mem <=> val_in_memory tv w p mem)
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `v` >> Cases_on `w` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule evaluate_types_length >> simp[] >> strip_tac >>
  imp_res_tac struct_has_type_values_have_types >>
  drule vyperTypeABITheory.evaluate_types_LIST_REL >> strip_tac >>
  imp_res_tac abi_encoder_list_conversion >>
  gvs[MAP_ZIP, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[val_in_memory_def, valueEncodingProofsTheory.fields_in_memory_tuple, MAP_ZIP] >>
  irule entry_tuple_memory_congruence >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> conj_tac
  >- (`MEM (EL i (MAP FST args), EL i tvs) (ZIP (MAP FST args,tvs))` by
        (simp[MEM_EL] >> qexists_tac `i` >> simp[EL_ZIP]) >>
      drule MEM_type_value_size_StructTV >> simp[type_value_size_def]) >>
  conj_tac
  >- (qexistsl [`EL i avs`, `env \\ nsid`, `EL i (MAP SND args)`] >> simp[]) >>
  simp[]
QED

Theorem entry_common_conversion_memory:
  !tv env ty v w av p mem.
    evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ value_has_type tv w /\
    vyper_to_abi env ty v = SOME av /\ vyper_to_abi env ty w = SOME av ==>
    (val_in_memory tv v p mem <=> val_in_memory tv w p mem)
Proof
  gen_tac >> completeInduct_on `type_value_size tv` >> rpt strip_tac >>
  Cases_on `ty`
  >- (drule evaluate_type_base_result >> strip_tac >> gvs[] >>
      gvs[Once vyper_to_abi_def] >> irule entry_base_common_conversion_memory >>
      metis_tac[])
  >- (irule entry_tuple_common_conversion_memory >> simp[] >> metis_tac[])
  >- (irule entry_array_common_conversion_memory >> simp[] >> metis_tac[])
  >- (irule entry_struct_common_conversion_memory >> simp[] >> metis_tac[]) >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v'` >> Cases_on `w` >>
  gvs[value_has_type_def, Once vyper_to_abi_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry common conversion inherited admission"
  end) [entry_tuple_common_conversion_memory, entry_array_common_conversion_memory,
        entry_struct_common_conversion_memory, entry_common_conversion_memory];
