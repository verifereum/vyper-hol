(*
 * ABI decode/encode typing helper lemmas for fresh Vyper type soundness.
 *)

Theory vyperTypeABI
Ancestors
  list rich_list arithmetic finite_map option pair sorting
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperTyping vyperEncodeDecode vyperTypeValues vyperTypeDefaults
Libs
  wordsLib

Theorem OPT_MMAP_LIST_REL:
  !f xs ys. OPT_MMAP f xs = SOME ys ==>
    LIST_REL (\x y. f x = SOME y) xs ys
Proof
  Induct_on `xs` >> simp[OPT_MMAP_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem OPT_MMAP_LENGTH:
  !f xs ys. OPT_MMAP f xs = SOME ys ==> LENGTH ys = LENGTH xs
Proof
  Induct_on `xs` >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> Cases_on `f h` >> simp[] >>
  Cases_on `OPT_MMAP f xs` >> simp[] >>
  strip_tac >> gvs[] >> res_tac
QED

Theorem evaluate_types_LIST_REL:
  !tenv ts tvs. evaluate_types tenv ts [] = SOME tvs ==>
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs
Proof
  rpt strip_tac >> gvs[evaluate_types_OPT_MMAP] >>
  irule OPT_MMAP_LIST_REL >> simp[]
QED

Theorem enumerate_static_array_sorted_aux:
  !d n vs. SORTED $< (MAP FST (enumerate_static_array d n vs)) /\
           EVERY (\k. n <= k) (MAP FST (enumerate_static_array d n vs))
Proof
  Induct_on `vs` >>
  simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (first_x_assum (qspecl_then [`d`, `SUC n`] strip_assume_tac) >>
      simp[] >> irule EVERY_MONOTONIC >>
      qexists_tac `\k. SUC n <= k` >> simp[])
  >> first_x_assum (qspecl_then [`d`, `SUC n`] strip_assume_tac) >>
  simp[sortingTheory.SORTED_DEF] >>
  reverse conj_tac
  >- (irule EVERY_MONOTONIC >>
      qexists_tac `\k. SUC n <= k` >> simp[])
  >> Cases_on `MAP FST (enumerate_static_array d (SUC n) vs)` >> simp[] >>
  gvs[EVERY_DEF]
QED

Theorem enumerate_static_array_sorted:
  !d n vs. SORTED $< (MAP FST (enumerate_static_array d n vs))
Proof
  metis_tac[enumerate_static_array_sorted_aux]
QED

Theorem values_have_types_REPLICATE_inv:
  !n tv vs. values_have_types (REPLICATE n tv) vs ==>
    all_have_type tv vs /\ LENGTH vs = n
Proof
  Induct >> simp[value_has_type_def] >>
  Cases_on `vs` >> simp[value_has_type_def] >> metis_tac[]
QED

Theorem struct_has_type_ZIP:
  !names tvs vs. values_have_types tvs vs /\ LENGTH names = LENGTH tvs ==>
    struct_has_type (ZIP(names,tvs)) (ZIP(names,vs))
Proof
  Induct >> rpt gen_tac >>
  (Cases_on `tvs` >> Cases_on `vs` >> simp[value_has_type_def]) >>
  strip_tac >> gvs[]
QED

Theorem abi_to_vyper_well_typed:
  (!tenv typ av v tv.
    abi_to_vyper tenv typ av = SOME v /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v) /\
  (!tenv ts avs vs tvs.
    abi_to_vyper_list tenv ts avs = SOME vs /\
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs ==>
    values_have_types tvs vs)
Proof
  ho_match_mp_tac abi_to_vyper_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[abi_to_vyper_def, AllCaseEqs(), PULL_EXISTS]
  >> TRY (simp[evaluate_type_def, AllCaseEqs(), check_IntV_def,
               value_has_type_def, within_int_bound_def,
               compatible_bound_def, integerTheory.INT_OF_NUM,
               integerTheory.NUM_OF_INT, LET_THM] >>
          rpt strip_tac >>
          gvs[value_has_type_def, within_int_bound_def,
              compatible_bound_def] >> NO_TAC)
  >> TRY (simp[value_has_type_def] >> NO_TAC)
  >> TRY (rpt strip_tac >> gvs[value_has_type_def] >> NO_TAC)
  >> TRY (strip_tac >> rpt gen_tac >>
          simp[evaluate_type_def, AllCaseEqs(), LET_THM] >>
          rpt strip_tac >> gvs[value_has_type_def] >>
          first_x_assum irule >> simp[] >>
          irule evaluate_types_LIST_REL >> simp[] >> NO_TAC)
  >> rpt strip_tac >>
  qpat_x_assum `evaluate_type _ _ = SOME _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [evaluate_type_def, AllCaseEqs(), LET_THM]) >>
  gvs[value_has_type_def]
  >- (first_x_assum
        (qspec_then `REPLICATE (LENGTH avs) tv'` mp_tac) >>
      simp[rich_listTheory.LIST_REL_REPLICATE_same] >> strip_tac >>
      imp_res_tac values_have_types_REPLICATE_inv >>
      Cases_on `b` >>
      gvs[make_array_value_def, value_has_type_def, compatible_bound_def,
          enumerate_static_array_sorted, all_have_type_EVERY] >>
      irule sparse_has_type_enumerate >> simp[])
  >> first_x_assum (qspec_then `tvs` mp_tac) >>
  simp[] >> (impl_tac >- (irule evaluate_types_LIST_REL >> simp[])) >>
  strip_tac >>
  irule struct_has_type_ZIP >>
  conj_tac >- (
    qpat_x_assum `evaluate_types _ _ _ = _` mp_tac >>
    simp[evaluate_types_OPT_MMAP] >> strip_tac >>
    imp_res_tac OPT_MMAP_LENGTH >> simp[LENGTH_MAP]) >>
  first_assum ACCEPT_TAC
QED

Theorem evaluate_abi_decode_well_typed:
  evaluate_abi_decode tenv typ bs = INL v /\
  evaluate_type tenv typ = SOME tv ==>
  value_has_type tv v
Proof
  rw[evaluate_abi_decode_def, AllCaseEqs(), LET_THM] >>
  drule_all (cj 1 abi_to_vyper_well_typed) >> simp[]
QED

(* TODO: AbiEncode result typing needs a static encoded-size bound in the type system. *)
