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

Theorem ceil32_mono:
  m <= n ==> ceil32 m <= ceil32 n
Proof
  rw[contractABITheory.ceil32_def] >>
  `m + 31 <= n + 31` by simp[] >>
  irule DIV_LE_MONOTONE >> simp[]
QED

Theorem all_have_type_values_have_types_REPLICATE:
  !tv vs. all_have_type tv vs ==>
    values_have_types (REPLICATE (LENGTH vs) tv) vs
Proof
  Induct_on `vs` >> simp[value_has_type_def]
QED

Theorem enc_tuple_acc_length_bound[local]:
  !ts vs hl tl hds tls.
    has_types ts vs ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  rw[Once contractABITheory.enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
     MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  TRY (
    first_x_assum drule >>
    disch_then (qspecl_then
      [`hl`, `tl + LENGTH (enc h' h)`,
       `word_to_bytes (n2w (hl + tl) : bytes32) T::hds`,
       `enc h' h::tls`] mp_tac) >>
    simp[byteTheory.LENGTH_word_to_bytes] >> decide_tac) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`hl`, `tl`, `enc h' h::hds`, `[]::tls`] mp_tac) >>
  simp[] >>
  `LENGTH (enc h' h) = static_length h'` by
    (irule (cj 1 contractABITheory.enc_has_static_length) >> simp[]) >>
  decide_tac
QED

Theorem enc_tuple_length_bound[local]:
  !ts vs.
    has_types ts vs ==>
    LENGTH (enc (Tuple ts) (ListV vs)) <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)
Proof
  rw[Once contractABITheory.enc_def] >>
  qspecl_then [`ts`, `vs`, `head_lengths ts 0`, `0`, `[]`, `[]`] mp_tac
    enc_tuple_acc_length_bound >>
  simp[] >> decide_tac
QED

Theorem SUM_MAP2_REPLICATE_enc_bound[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded
Proof
  Induct_on `vs` >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `elem_bound`, `embedded`] mp_tac) >>
  impl_tac >- (rw[] >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  Cases_on `is_dynamic t` >> gvs[] >>
  first_x_assum (qspec_then `h` mp_tac) >> simp[] >>
  strip_tac >> simp[MULT_CLAUSES] >> decide_tac
QED

Theorem enc_dyn_array_same_length_bound[local]:
  !t vs elem_bound embedded.
    have_type t vs /\
    (!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
    (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded ==>
    LENGTH (enc (Array NONE t) (ListV vs)) <= 32 + LENGTH vs * embedded
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def, byteTheory.LENGTH_word_to_bytes] >>
  qmatch_goalsub_abbrev_tac `LENGTH et <= _` >>
  `LENGTH et <= 32 +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
                (REPLICATE (LENGTH vs) t) vs)` by
    (qunabbrev_tac `et` >>
     qspecl_then [`REPLICATE (LENGTH vs) t`, `vs`,
       `head_lengths (REPLICATE (LENGTH vs) t) 0`, `0`,
       `[word_to_bytes (n2w (LENGTH vs) : bytes32) T]`, `[]`] mp_tac
       enc_tuple_acc_length_bound >>
     simp[GSYM contractABITheory.have_type_has_types_REPLICATE,
          byteTheory.LENGTH_word_to_bytes, MULT_COMM] >> decide_tac) >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
             (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded` by
    (qspecl_then [`t`, `vs`, `elem_bound`, `embedded`] mp_tac
       SUM_MAP2_REPLICATE_enc_bound >> simp[]) >>
  decide_tac
QED

Theorem enc_fixed_array_same_length_bound[local]:
  !n t vs elem_bound embedded.
    has_type (Array (SOME n) t) (ListV vs) /\
    (!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
    (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded ==>
    LENGTH (enc (Array (SOME n) t) (ListV vs)) <= n * embedded
Proof
  rpt strip_tac >>
  gvs[contractABITheory.has_type_def, contractABITheory.valid_length_def] >>
  simp[Once contractABITheory.enc_def] >>
  qmatch_goalsub_abbrev_tac `LENGTH et <= _` >>
  `LENGTH et <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
                (REPLICATE (LENGTH vs) t) vs)` by
    (qunabbrev_tac `et` >>
     qspecl_then [`REPLICATE (LENGTH vs) t`, `vs`,
       `head_lengths (REPLICATE (LENGTH vs) t) 0`, `0`, `[]`, `[]`] mp_tac
       enc_tuple_acc_length_bound >>
     simp[]) >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
             (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded` by
    (qspecl_then [`t`, `vs`, `elem_bound`, `embedded`] mp_tac
       SUM_MAP2_REPLICATE_enc_bound >> simp[]) >>
  decide_tac
QED

Theorem enc_tuple_acc_length_bound_actual[local]:
  !ts vs hl tl hds tls.
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else LENGTH (enc t v)) ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >>
  rw[Once contractABITheory.enc_def, LENGTH_FLAT, REV_REVERSE_LEM,
     MAP_REVERSE, SUM_REVERSE, SUM_APPEND] >>
  Cases_on `is_dynamic h'` >> gvs[]
  >- (qpat_x_assum `!vs hl tl hds tls. _` (qspecl_then
        [`t`, `hl`, `tl + LENGTH (enc h' h)`,
         `word_to_bytes (n2w (hl + tl) : bytes32) T::hds`,
         `enc h' h::tls`] mp_tac) >>
      simp[byteTheory.LENGTH_word_to_bytes] >> decide_tac) >>
  qpat_x_assum `!vs hl tl hds tls. _`
    (qspecl_then [`t`, `hl`, `tl`, `enc h' h::hds`, `[]::tls`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem SUM_MAP2_static_premise_bound[local]:
  !ts vs.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else LENGTH (enc t v)) ts vs) <=
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)
Proof
  Induct_on `ts` >> Cases_on `vs` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!vs. _` (qspec_then `t` mp_tac) >>
  impl_tac >- (rw[] >> first_x_assum irule >> simp[]) >>
  strip_tac >>
  Cases_on `is_dynamic h'` >> gvs[] >>
  qpat_x_assum `!t' v. _` (qspecl_then [`h'`, `h`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem enc_tuple_acc_length_bound_static_premise[local]:
  !ts vs hl tl hds tls.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc_tuple hl tl ts vs hds tls) <=
      SUM (MAP LENGTH hds) + SUM (MAP LENGTH tls) +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)
Proof
  rpt strip_tac >>
  qspecl_then [`ts`, `vs`] mp_tac SUM_MAP2_static_premise_bound >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`ts`, `vs`, `hl`, `tl`, `hds`, `tls`] mp_tac
    enc_tuple_acc_length_bound_actual >>
  decide_tac
QED

Theorem enc_tuple_length_bound_static_premise[local]:
  !ts vs.
    (!t v. MEM (t,v) (ZIP (ts,vs)) /\ ~is_dynamic t ==>
           LENGTH (enc t v) <= static_length t) ==>
    LENGTH (enc (Tuple ts) (ListV vs)) <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t) ts vs)
Proof
  rw[Once contractABITheory.enc_def] >>
  qspecl_then [`ts`, `vs`, `head_lengths ts 0`, `0`, `[]`, `[]`] mp_tac
    enc_tuple_acc_length_bound_static_premise >>
  simp[] >> decide_tac
QED

Theorem SUM_MAP2_REPLICATE_enc_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded
Proof
  Induct_on `vs` >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`t`, `elem_bound`, `embedded`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac
     >- (rw[] >> first_x_assum irule >> simp[])
     >- (strip_tac >> rw[] >> first_x_assum irule >> simp[]) >>
     Cases_on `is_dynamic t` >> gvs[] >> decide_tac) >>
  strip_tac >>
  Cases_on `is_dynamic t` >> gvs[] >> simp[MULT_CLAUSES]
  >- (qpat_x_assum `!v. _ ==> LENGTH (enc t v) <= elem_bound`
        (qspec_then `h` mp_tac) >> simp[] >> decide_tac) >>
  decide_tac
QED

Theorem MEM_ZIP_REPLICATE_SAME[local]:
  !t vs t' v.
    MEM (t',v) (ZIP (REPLICATE (LENGTH vs) t,vs)) <=> t' = t /\ MEM v vs
Proof
  rw[MEM_ZIP, EQ_IMP_THM]
  >- simp[EL_REPLICATE]
  >- (irule EL_MEM >> simp[]) >>
  gvs[MEM_EL] >> qexists `n` >> simp[EL_REPLICATE]
QED

Theorem enc_dyn_array_same_length_bound_static_premise[local]:
  !t vs elem_bound embedded.
    ((!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array NONE t) (ListV vs)) <= 32 + LENGTH vs * embedded
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def, byteTheory.LENGTH_word_to_bytes] >>
  qmatch_goalsub_abbrev_tac `LENGTH et <= _` >>
  `LENGTH et <= 32 +
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
                (REPLICATE (LENGTH vs) t) vs)` by
    (qunabbrev_tac `et` >>
     qspecl_then [`REPLICATE (LENGTH vs) t`, `vs`,
       `head_lengths (REPLICATE (LENGTH vs) t) 0`, `0`,
       `[word_to_bytes (n2w (LENGTH vs) : bytes32) T]`, `[]`] mp_tac
       enc_tuple_acc_length_bound_static_premise >>
     simp[MEM_ZIP_REPLICATE_SAME, byteTheory.LENGTH_word_to_bytes]) >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
             (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded` by
    (qspecl_then [`t`, `vs`, `elem_bound`, `embedded`] mp_tac
       SUM_MAP2_REPLICATE_enc_bound_static_premise >> simp[]) >>
  decide_tac
QED

Theorem enc_fixed_array_same_length_bound_static_premise[local]:
  !n t vs elem_bound embedded.
    (LENGTH vs <= n /\
     (!v. MEM v vs ==> LENGTH (enc t v) <= elem_bound) /\
     (~is_dynamic t ==> !v. MEM v vs ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc (Array (SOME n) t) (ListV vs)) <= n * embedded
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def] >>
  qmatch_goalsub_abbrev_tac `LENGTH et <= _` >>
  `LENGTH et <=
      SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
                (REPLICATE (LENGTH vs) t) vs)` by
    (qunabbrev_tac `et` >>
     qspecl_then [`REPLICATE (LENGTH vs) t`, `vs`,
       `head_lengths (REPLICATE (LENGTH vs) t) 0`, `0`, `[]`, `[]`] mp_tac
       enc_tuple_acc_length_bound_static_premise >>
     simp[MEM_ZIP_REPLICATE_SAME]) >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
             (REPLICATE (LENGTH vs) t) vs) <= LENGTH vs * embedded` by
    (qspecl_then [`t`, `vs`, `elem_bound`, `embedded`] mp_tac
       SUM_MAP2_REPLICATE_enc_bound_static_premise >> simp[]) >>
  `LENGTH vs * embedded <= n * embedded` by simp[] >>
  decide_tac
QED

Theorem vyper_to_abi_type_dynamic_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     is_dynamic (vyper_to_abi_type tenv typ) = vyper_is_dynamic tenv typ) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_to_abi_type_def, vyper_is_dynamic_def,
       AllCaseEqs(), LET_THM, PULL_EXISTS] >>
  rpt strip_tac >>
  TRY (Cases_on `bd`) >>
  gvs[vyper_to_abi_type_def, vyper_is_dynamic_def]
QED

Theorem vyper_to_abi_type_dynamic[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     is_dynamic (vyper_to_abi_type tenv typ) = vyper_is_dynamic tenv typ) /\
  (!tenv ts tvs.
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs ==>
     any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  conj_tac >- metis_tac[vyper_to_abi_type_dynamic_eval] >>
  Induct_on `ts` >> Cases_on `tvs` >>
  simp[vyper_to_abi_type_def, vyper_is_dynamic_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[vyper_to_abi_type_dynamic_eval]
QED

Theorem vyper_to_abi_static_length_bound_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv /\ ~vyper_is_dynamic tenv typ ==>
     static_length (vyper_to_abi_type tenv typ) = vyper_abi_size_bound tenv typ) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs /\ ~vyper_any_dynamic tenv ts ==>
     static_length (Tuple (vyper_to_abi_types tenv ts)) =
     vyper_abi_size_bound_list tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_to_abi_type_def, vyper_is_dynamic_def,
       vyper_abi_size_bound_def, AllCaseEqs(), LET_THM, PULL_EXISTS] >>
  rpt strip_tac >>
  TRY (Cases_on `bd`) >>
  gvs[vyper_to_abi_type_def, vyper_is_dynamic_def,
      vyper_abi_size_bound_def, contractABITheory.static_length_Tuple_SUM]
QED

Theorem vyper_to_abi_static_length_bound[local]:
  !tenv typ tv.
    evaluate_type tenv typ = SOME tv /\ ~vyper_is_dynamic tenv typ ==>
    static_length (vyper_to_abi_type tenv typ) = vyper_abi_size_bound tenv typ
Proof
  metis_tac[vyper_to_abi_static_length_bound_eval]
QED

Theorem vyper_to_abi_embedded_head_bound[local]:
  !tenv typ tv.
    evaluate_type tenv typ = SOME tv ==>
    (if is_dynamic (vyper_to_abi_type tenv typ)
     then 32 + vyper_abi_size_bound tenv typ
     else static_length (vyper_to_abi_type tenv typ)) <=
    vyper_abi_embedded_size tenv typ
Proof
  rpt strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  Cases_on `vyper_is_dynamic tenv typ` >>
  gvs[vyper_abi_size_bound_def] >>
  drule_all vyper_to_abi_static_length_bound >> simp[]
QED

Theorem vyper_abi_size_bound_le_singleton_tuple[local]:
  !tenv typ. vyper_abi_size_bound tenv typ <=
              vyper_abi_size_bound tenv (TupleT [typ])
Proof
  simp[vyper_abi_size_bound_def] >> rpt gen_tac >>
  Cases_on `vyper_is_dynamic tenv typ` >> simp[]
QED

Theorem enc_fixed_array_replicate_tuple_bound_static_premise[local]:
  !n t v elem_bound embedded.
    (LENGTH (enc t v) <= elem_bound /\
     (~is_dynamic t ==> LENGTH (enc t v) <= static_length t) /\
     (if is_dynamic t then 32 + elem_bound else static_length t) <= embedded) ==>
    LENGTH (enc_tuple (head_lengths (REPLICATE n t) 0) 0
              (REPLICATE n t) (REPLICATE n v) [] []) <= n * embedded
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `t`, `REPLICATE n v`, `elem_bound`, `embedded`] mp_tac
    enc_fixed_array_same_length_bound_static_premise >>
  simp[Once contractABITheory.enc_def]
QED

Theorem default_fixed_array_replicate_tuple_bound_from_elem[local]:
  !tenv typ tv n.
    evaluate_type tenv typ = SOME tv /\
    LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
    vyper_abi_size_bound tenv typ ==>
    LENGTH (enc_tuple (head_lengths (REPLICATE n (vyper_to_abi_type tenv typ)) 0) 0
              (REPLICATE n (vyper_to_abi_type tenv typ))
              (REPLICATE n (default_to_abi tv)) [] []) <=
    n * (if vyper_is_dynamic tenv typ then vyper_abi_size_bound tenv typ + 32
         else vyper_abi_size_bound tenv typ)
Proof
  rpt strip_tac >>
  irule enc_fixed_array_replicate_tuple_bound_static_premise >>
  conj_tac
  >- (qexists `vyper_abi_size_bound tenv typ` >>
      simp[] >>
      drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
      Cases_on `vyper_is_dynamic tenv typ` >> gvs[] >>
      drule_all vyper_to_abi_static_length_bound >> simp[]) >>
  strip_tac >>
  drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >> gvs[] >>
  drule_all vyper_to_abi_static_length_bound >> simp[]
QED

Definition default_to_abi_elem_bound_rel_def[local]:
  default_to_abi_elem_bound_rel tenv typ tv <=>
    evaluate_type tenv typ = SOME tv /\
    LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
      vyper_abi_size_bound tenv typ /\
    (~vyper_is_dynamic tenv typ ==>
     LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
       static_length (vyper_to_abi_type tenv typ))
End

Theorem default_to_abi_elem_embedded_size_bound[local]:
  !tenv typ tv.
    default_to_abi_elem_bound_rel tenv typ tv ==>
    (if is_dynamic (vyper_to_abi_type tenv typ)
     then 32 + LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv))
     else static_length (vyper_to_abi_type tenv typ)) <=
    vyper_abi_embedded_size tenv typ
Proof
  rw[default_to_abi_elem_bound_rel_def] >>
  drule_all vyper_to_abi_embedded_head_bound >>
  Cases_on `is_dynamic (vyper_to_abi_type tenv typ)` >> gvs[] >> decide_tac
QED

Theorem default_to_abi_tuple_static_premise_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (\typ tv.
      evaluate_type tenv typ = SOME tv /\
      LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
        vyper_abi_size_bound tenv typ /\
      (~vyper_is_dynamic tenv typ ==>
       LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
         static_length (vyper_to_abi_type tenv typ))) ts tvs ==>
    !t v.
      MEM (t,v) (ZIP (vyper_to_abi_types tenv ts, MAP default_to_abi tvs)) /\
      ~is_dynamic t ==>
      LENGTH (enc t v) <= static_length t
Proof
  rpt gen_tac >>
  qid_spec_tac `tvs` >> Induct_on `ts` >> Cases_on `tvs` >>
  simp[vyper_to_abi_type_def, MEM_ZIP] >> rpt strip_tac >> gvs[]
  >- (drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >> gvs[]) >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`t'`, `v`] mp_tac) >> simp[]
QED

Theorem default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (\typ tv.
      evaluate_type tenv typ = SOME tv /\
      LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
        vyper_abi_size_bound tenv typ /\
      (~vyper_is_dynamic tenv typ ==>
       LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
         static_length (vyper_to_abi_type tenv typ))) ts tvs ==>
    SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (vyper_to_abi_types tenv ts) (MAP default_to_abi tvs)) <=
    vyper_abi_size_bound_list tenv ts
Proof
  Induct_on `ts`
  >- simp[vyper_to_abi_type_def, vyper_abi_size_bound_def] >>
  rpt gen_tac >> Cases_on `tvs` >>
  simp[vyper_to_abi_type_def, vyper_abi_size_bound_def] >> rpt strip_tac >> gvs[] >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                         else static_length t)
              (vyper_to_abi_types tenv ts) (MAP default_to_abi t)) <=
     vyper_abi_size_bound_list tenv ts` by
    (first_x_assum (qspecl_then [`tenv`, `t`] mp_tac) >> simp[]) >>
  drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  Cases_on `vyper_is_dynamic tenv h`
  >- (fs[vyper_abi_size_bound_def] >> decide_tac) >>
  fs[vyper_abi_size_bound_def] >>
  drule_all vyper_to_abi_static_length_bound >> simp[] >> decide_tac
QED

Theorem default_to_abi_tuple_bound_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (\typ tv.
      evaluate_type tenv typ = SOME tv /\
      LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
        vyper_abi_size_bound tenv typ /\
      (~vyper_is_dynamic tenv typ ==>
       LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
         static_length (vyper_to_abi_type tenv typ))) ts tvs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts))
                (ListV (MAP default_to_abi tvs))) <=
    vyper_abi_size_bound_list tenv ts
Proof
  rpt strip_tac >>
  `LENGTH (enc (Tuple (vyper_to_abi_types tenv ts))
               (ListV (MAP default_to_abi tvs))) <=
   SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                        else static_length t)
             (vyper_to_abi_types tenv ts) (MAP default_to_abi tvs))` by
    (irule enc_tuple_length_bound_static_premise >>
     metis_tac[default_to_abi_tuple_static_premise_from_LIST_REL]) >>
  `SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                        else static_length t)
             (vyper_to_abi_types tenv ts) (MAP default_to_abi tvs)) <=
   vyper_abi_size_bound_list tenv ts` by
    (irule default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL >> simp[]) >>
  decide_tac
QED

Theorem default_to_abi_enc_tuple_bound_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (default_to_abi_elem_bound_rel tenv) ts tvs ==>
    LENGTH (enc_tuple (head_lengths (vyper_to_abi_types tenv ts) 0) 0
              (vyper_to_abi_types tenv ts) (MAP default_to_abi tvs) [] []) <=
    vyper_abi_size_bound_list tenv ts
Proof
  rpt strip_tac >>
  `LIST_REL (\typ tv.
      evaluate_type tenv typ = SOME tv /\
      LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
        vyper_abi_size_bound tenv typ /\
      (~vyper_is_dynamic tenv typ ==>
       LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
         static_length (vyper_to_abi_type tenv typ))) ts tvs` by
    (qpat_x_assum `LIST_REL (default_to_abi_elem_bound_rel tenv) ts tvs` mp_tac >>
     qid_spec_tac `tvs` >> Induct_on `ts` >> Cases_on `tvs` >>
     simp[default_to_abi_elem_bound_rel_def]) >>
  qspecl_then [`tenv`, `ts`, `tvs`] mp_tac default_to_abi_tuple_bound_from_LIST_REL >>
  simp[Once contractABITheory.enc_def]
QED

Theorem MAP_default_to_abi_SND_ZIP[local]:
  !names tvs.
    LENGTH names = LENGTH tvs ==>
    MAP (default_to_abi o SND) (ZIP (names,tvs)) = MAP default_to_abi tvs
Proof
  simp[MAP_ZIP]
QED

Theorem default_to_abi_size_bound_list_static_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (default_to_abi_elem_bound_rel tenv) ts tvs /\
    ~vyper_any_dynamic tenv ts ==>
    vyper_abi_size_bound_list tenv ts =
    SUM (MAP static_length (vyper_to_abi_types tenv ts))
Proof
  Induct_on `ts` >> Cases_on `tvs` >>
  simp[vyper_abi_size_bound_def, vyper_to_abi_type_def,
       vyper_is_dynamic_def] >>
  rpt strip_tac >>
  gvs[default_to_abi_elem_bound_rel_def, vyper_abi_size_bound_def] >>
  first_x_assum (qspecl_then [`tenv`, `t`] mp_tac) >> simp[] >> strip_tac >>
  drule_all vyper_to_abi_static_length_bound >> strip_tac >>
  gvs[vyper_abi_size_bound_def]
QED

Theorem default_to_abi_enc_tuple_static_bound_from_LIST_REL[local]:
  !tenv ts tvs.
    LIST_REL (default_to_abi_elem_bound_rel tenv) ts tvs /\
    ~vyper_any_dynamic tenv ts ==>
    LENGTH (enc_tuple (head_lengths (vyper_to_abi_types tenv ts) 0) 0
              (vyper_to_abi_types tenv ts) (MAP default_to_abi tvs) [] []) <=
    SUM (MAP static_length (vyper_to_abi_types tenv ts))
Proof
  rpt strip_tac >>
  drule_all default_to_abi_enc_tuple_bound_from_LIST_REL >> strip_tac >>
  drule_all default_to_abi_size_bound_list_static_from_LIST_REL >> strip_tac >>
  gvs[]
QED

Theorem default_to_abi_elem_bound_rel_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     default_to_abi_elem_bound_rel tenv typ tv) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LIST_REL (default_to_abi_elem_bound_rel tenv) ts dtvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, default_to_abi_elem_bound_rel_def,
       default_to_abi_def, default_to_abi_list_MAP,
       default_to_abi_fields_MAP, vyper_to_abi_type_def,
       vyper_abi_size_bound_def, AllCaseEqs(), LET_THM, PULL_EXISTS,
       contractABITheory.static_length_Tuple_SUM, LENGTH_TAKE_EQ,
       byteTheory.LENGTH_word_to_bytes] >>
  rpt strip_tac >>
  gvs[default_to_abi_elem_bound_rel_def, default_to_abi_def,
      default_to_abi_list_MAP, default_to_abi_fields_MAP,
      vyper_to_abi_type_def, vyper_abi_size_bound_def, LET_THM,
      LENGTH_TAKE_EQ, byteTheory.LENGTH_word_to_bytes] >>
  TRY (gvs[vyper_is_dynamic_def] >> NO_TAC) >>
  TRY (irule ceil32_mono >> simp[]) >>
  TRY (Cases_on `bd` >> gvs[default_to_abi_def, vyper_to_abi_type_def,
                              vyper_abi_size_bound_def, vyper_is_dynamic_def]) >>
  TRY (
    qmatch_goalsub_abbrev_tac `LENGTH (enc (Array NONE at) (ListV [])) <= bnd` >>
    `LENGTH (enc (Array NONE at) (ListV [])) <= 32` by
      (qspecl_then [`at`, `[]`, `vyper_abi_size_bound tenv typ`,
                    `vyper_abi_embedded_size tenv typ`] mp_tac
         enc_dyn_array_same_length_bound_static_premise >>
       simp[Abbr `at`]) >>
    simp[Abbr `bnd`] >> decide_tac >> NO_TAC) >>
  TRY (
    qmatch_goalsub_abbrev_tac `LENGTH (enc (Array (SOME n) at) (ListV vs')) <= bnd` >>
    `LENGTH (enc (Array (SOME n) at) (ListV vs')) <=
       n * vyper_abi_embedded_size tenv typ` by
      (qspecl_then [`n`, `at`, `vs'`, `vyper_abi_size_bound tenv typ`,
                    `vyper_abi_embedded_size tenv typ`] mp_tac
         enc_fixed_array_same_length_bound_static_premise >>
       simp[Abbr `at`, Abbr `vs'`] >>
       rpt strip_tac
       >- (first_x_assum irule >> simp[])
       >- (drule_all vyper_to_abi_static_length_bound >> simp[]) >>
       drule_all vyper_to_abi_embedded_head_bound >> simp[]) >>
    simp[Abbr `bnd`] >> NO_TAC) >>
  TRY (
    qpat_x_assum `evaluate_types _ _ [] = SOME tvs` mp_tac >>
    simp[evaluate_types_OPT_MMAP] >> strip_tac >>
    irule_at Any OPT_MMAP_LIST_REL >> simp[] >> NO_TAC) >>
  TRY (
    qexists `[]` >> simp[] >> NO_TAC) >>
  TRY (
    first_x_assum drule >> strip_tac >>
    first_x_assum drule >> strip_tac >>
    qexists `tv::dtvs` >> gvs[] >> NO_TAC) >>
  TRY (
    irule default_to_abi_enc_tuple_bound_from_LIST_REL >> simp[] >> NO_TAC) >>
  TRY (
    gvs[vyper_is_dynamic_def] >>
    irule default_to_abi_enc_tuple_static_bound_from_LIST_REL >> simp[] >> NO_TAC) >>
  TRY (
    `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
    simp[MAP_default_to_abi_SND_ZIP] >>
    irule default_to_abi_enc_tuple_bound_from_LIST_REL >> simp[] >> NO_TAC) >>
  TRY (
    `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
    simp[MAP_default_to_abi_SND_ZIP] >>
    gvs[vyper_is_dynamic_def, LET_THM] >>
    irule default_to_abi_enc_tuple_static_bound_from_LIST_REL >> simp[] >> NO_TAC) >>
  TRY (irule default_fixed_array_replicate_tuple_bound_from_elem >> simp[] >> NO_TAC) >>
  TRY (
    qspecl_then [`n`, `vyper_to_abi_type tenv typ`, `default_to_abi tv'`,
                 `vyper_abi_size_bound tenv typ`,
                 `static_length (vyper_to_abi_type tenv typ)`] mp_tac
      enc_fixed_array_replicate_tuple_bound_static_premise >>
    impl_tac >-
      (rpt conj_tac
       >- simp[]
       >- simp[] >>
       drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >> gvs[]) >>
    simp[] >> NO_TAC) >>
  TRY (
    drule_all vyper_to_abi_static_length_bound >> strip_tac >>
    gvs[] >>
    irule default_fixed_array_replicate_tuple_bound_from_elem >> simp[] >> NO_TAC) >>
  TRY (simp[LENGTH_FLAT, REV_REVERSE_LEM, byteTheory.LENGTH_word_to_bytes] >> decide_tac >> NO_TAC) >>
  FAIL_TAC "probe_c444_elem_bound_rel_eval"
QED

Theorem default_to_abi_enc_length_bound_eval[local]:
  (!tenv typ tv.
     evaluate_type tenv typ = SOME tv ==>
     LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
     vyper_abi_size_bound tenv typ) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     ?dtvs.
       tvs = REVERSE acc ++ dtvs /\
       LENGTH (enc (Tuple (vyper_to_abi_types tenv ts))
                   (ListV (MAP default_to_abi dtvs))) <=
       vyper_abi_size_bound_list tenv ts /\
       SUM (MAP2 (\t v. if is_dynamic t then 32 + LENGTH (enc t v)
                            else static_length t)
                 (vyper_to_abi_types tenv ts) (MAP default_to_abi dtvs)) <=
       vyper_abi_size_bound_list tenv ts /\
       (!t v. MEM (t,v) (ZIP (vyper_to_abi_types tenv ts,
                               MAP default_to_abi dtvs)) /\
              ~is_dynamic t ==>
              LENGTH (enc t v) <= static_length t))
Proof
  conj_tac
  >- (rpt strip_tac >>
      drule (cj 1 default_to_abi_elem_bound_rel_eval) >>
      simp[default_to_abi_elem_bound_rel_def]) >>
  rpt strip_tac >>
  drule (cj 2 default_to_abi_elem_bound_rel_eval) >>
  disch_then (qx_choose_then `dtvs` strip_assume_tac) >>
  qexists `dtvs` >> simp[] >>
  `LIST_REL (\typ tv.
      evaluate_type tenv typ = SOME tv /\
      LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
        vyper_abi_size_bound tenv typ /\
      (~vyper_is_dynamic tenv typ ==>
       LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
         static_length (vyper_to_abi_type tenv typ))) ts dtvs` by
    (irule LIST_REL_mono >>
     qexists `default_to_abi_elem_bound_rel tenv` >>
     simp[default_to_abi_elem_bound_rel_def]) >>
  ((conj_tac >- (irule default_to_abi_enc_tuple_bound_from_LIST_REL >> simp[])) >>
   (conj_tac >-
    (qspecl_then [`tenv`, `ts`, `dtvs`] mp_tac
       default_to_abi_tuple_SUM_MAP2_bound_from_LIST_REL >> simp[])) >>
   qspecl_then [`tenv`, `ts`, `dtvs`] mp_tac
     default_to_abi_tuple_static_premise_from_LIST_REL >> simp[])
QED

Theorem default_to_abi_enc_length_bound[local]:
  !tenv typ tv.
    evaluate_type tenv typ = SOME tv ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
    vyper_abi_size_bound tenv typ
Proof
  metis_tac[default_to_abi_enc_length_bound_eval]
QED

Theorem default_to_abi_static_enc_length_bound[local]:
  !tenv typ tv.
    evaluate_type tenv typ = SOME tv /\ ~vyper_is_dynamic tenv typ ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) (default_to_abi tv)) <=
    static_length (vyper_to_abi_type tenv typ)
Proof
  rpt strip_tac >>
  drule_all default_to_abi_enc_length_bound >> strip_tac >>
  drule_all vyper_to_abi_static_length_bound >> simp[]
QED




Theorem enc_string_length_bound[local]:
  !bs n. LENGTH bs <= n ==>
    LENGTH (enc String (BytesV bs)) <= ceil32 n + 32
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def, byteTheory.LENGTH_word_to_bytes] >>
  `ceil32 (LENGTH bs) <= ceil32 n` by (irule ceil32_mono >> simp[]) >>
  `LENGTH bs <= ceil32 (LENGTH bs)` by simp[] >>
  decide_tac
QED

Theorem enc_dynamic_bytes_length_bound[local]:
  !bs n. LENGTH bs <= n ==>
    LENGTH (enc (Bytes NONE) (BytesV bs)) <= ceil32 n + 32
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def, byteTheory.LENGTH_word_to_bytes] >>
  `ceil32 (LENGTH bs) <= ceil32 n` by (irule ceil32_mono >> simp[]) >>
  `LENGTH bs <= ceil32 (LENGTH bs)` by simp[] >>
  decide_tac
QED

Theorem enc_fixed_bytes_length_bound[local]:
  !bs n. LENGTH bs = n /\ n <= 32 ==>
    LENGTH (enc (Bytes (SOME n)) (BytesV bs)) <= 32
Proof
  rpt strip_tac >>
  simp[Once contractABITheory.enc_def, LENGTH_TAKE_EQ]
QED

Theorem vyper_to_abi_base_enc_length_bound[local]:
  !tenv bt v av tv.
    vyper_to_abi_base bt v = SOME av /\
    evaluate_type tenv (BaseT bt) = SOME tv /\
    value_has_type tv v ==>
    LENGTH (enc (vyper_base_to_abi_type bt) av) <=
    vyper_abi_size_bound tenv (BaseT bt)
Proof
  rpt gen_tac >> Cases_on `bt` >> Cases_on `v` >>
  simp[evaluate_type_def, vyper_to_abi_type_def,
       vyper_to_abi_base_def, vyper_abi_size_bound_def,
       value_has_type_def, within_int_bound_def, compatible_bound_def,
       AllCaseEqs(), LET_THM, LENGTH_MAP] >>
  rpt strip_tac >> gvs[value_has_type_def, vyper_abi_size_bound_def] >>
  simp[Once contractABITheory.enc_def, LENGTH_TAKE_EQ,
       byteTheory.LENGTH_word_to_bytes] >>
  TRY (`ceil32 (STRLEN s) <= ceil32 n` by (irule ceil32_mono >> simp[]) >>
       `STRLEN s <= ceil32 (STRLEN s)` by simp[] >> decide_tac >> NO_TAC) >>
  TRY (`ceil32 (LENGTH l) <= ceil32 n'` by (irule ceil32_mono >> simp[]) >>
       `LENGTH l <= ceil32 (LENGTH l)` by simp[] >> decide_tac >> NO_TAC) >>
  decide_tac
QED

Definition abi_av_bound_rel_def[local]:
  abi_av_bound_rel tenv typ tv av <=>
    evaluate_type tenv typ = SOME tv /\
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
      vyper_abi_size_bound tenv typ
End

Definition abi_av_list_bound_rel_def[local]:
  abi_av_list_bound_rel tenv [] [] [] = T /\
  abi_av_list_bound_rel tenv (typ::ts) (av::avs) (tv::tvs) =
    (abi_av_bound_rel tenv typ tv av /\
     abi_av_list_bound_rel tenv ts avs tvs) /\
  abi_av_list_bound_rel tenv _ _ _ = F
End

Definition sparse_values_have_type_def[local]:
  sparse_values_have_type tv sparse <=>
    !k v. MEM (k,v) sparse ==> value_has_type tv v
End

Theorem abi_av_bound_rel_static_premise[local]:
  !tenv typ tv av.
    abi_av_bound_rel tenv typ tv av /\
    ~is_dynamic (vyper_to_abi_type tenv typ) ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    static_length (vyper_to_abi_type tenv typ)
Proof
  rpt strip_tac >> gvs[abi_av_bound_rel_def] >>
  drule_all (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >> gvs[] >>
  drule_all vyper_to_abi_static_length_bound >> simp[]
QED

Theorem abi_av_list_static_premise[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    !t av.
      MEM (t,av) (ZIP (vyper_to_abi_types tenv ts, avs)) /\ ~is_dynamic t ==>
      LENGTH (enc t av) <= static_length t
Proof
  rpt gen_tac >> qid_spec_tac `avs` >> qid_spec_tac `tvs` >>
  Induct_on `ts` >> Cases_on `avs` >> Cases_on `tvs` >>
  simp[abi_av_list_bound_rel_def, vyper_to_abi_type_def, MEM_ZIP] >>
  rpt strip_tac >> gvs[]
  >- (drule_all abi_av_bound_rel_static_premise >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem abi_av_list_SUM_MAP2_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    SUM (MAP2 (\t av. if is_dynamic t then 32 + LENGTH (enc t av)
                          else static_length t)
              (vyper_to_abi_types tenv ts) avs) <=
    vyper_abi_size_bound_list tenv ts
Proof
  Induct_on `ts` >> Cases_on `avs` >> Cases_on `tvs` >>
  simp[abi_av_list_bound_rel_def, vyper_to_abi_type_def,
       vyper_abi_size_bound_def] >>
  rpt strip_tac >> gvs[abi_av_bound_rel_def] >>
  first_x_assum drule >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  Cases_on `vyper_is_dynamic tenv h''` >> gvs[vyper_abi_size_bound_def]
  >- (drule_all vyper_to_abi_static_length_bound >> simp[] >> decide_tac) >>
  decide_tac
QED

Theorem abi_av_list_tuple_bound[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts
Proof
  rpt strip_tac >>
  `LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
   SUM (MAP2 (\t av. if is_dynamic t then 32 + LENGTH (enc t av)
                        else static_length t)
             (vyper_to_abi_types tenv ts) avs)` by
    (irule enc_tuple_length_bound_static_premise >>
     metis_tac[abi_av_list_static_premise]) >>
  drule_all abi_av_list_SUM_MAP2_bound >> decide_tac
QED

Theorem abi_av_list_tuple_bound_enc_tuple[local]:
  !tenv ts avs tvs.
    abi_av_list_bound_rel tenv ts avs tvs ==>
    LENGTH
      (enc_tuple (head_lengths (vyper_to_abi_types tenv ts) 0) 0
         (vyper_to_abi_types tenv ts) avs [] []) <=
    vyper_abi_size_bound_list tenv ts
Proof
  rpt strip_tac >> drule_all abi_av_list_tuple_bound >>
  simp[Once contractABITheory.enc_def]
QED

Theorem abi_av_list_tuple_bound_from_eval_vht[local]:
  !tenv ts vs avs tv.
    (!tvs.
       LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
       values_have_types tvs vs ==>
       abi_av_list_bound_rel tenv ts avs tvs) /\
    evaluate_type tenv (TupleT ts) = SOME tv /\
    value_has_type tv (ArrayV (TupleV vs)) ==>
    LENGTH
      (enc_tuple (head_lengths (vyper_to_abi_types tenv ts) 0) 0
         (vyper_to_abi_types tenv ts) avs [] []) <=
    vyper_abi_size_bound tenv (TupleT ts)
Proof
  rpt strip_tac >>
  qpat_x_assum `evaluate_type tenv (TupleT ts) = SOME tv` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> gvs[value_has_type_def, vyper_abi_size_bound_def] >>
  `abi_av_list_bound_rel tenv ts avs tvs` by
    (first_x_assum irule >> simp[] >>
     irule evaluate_types_LIST_REL >> simp[]) >>
  drule_all abi_av_list_tuple_bound_enc_tuple >> simp[]
QED
Theorem abi_av_list_struct_bound_from_eval_vht[local]:
  !tenv nsid args fields avs tv.
    (!tvs.
       LIST_REL (\ty tv. evaluate_type (tenv \\ type_key nsid) ty = SOME tv)
         (MAP SND args) tvs /\
       values_have_types tvs (MAP SND fields) ==>
       abi_av_list_bound_rel (tenv \\ type_key nsid) (MAP SND args) avs tvs) /\
    FLOOKUP tenv (type_key nsid) = SOME (StructArgs args) /\
    evaluate_type tenv (StructT nsid) = SOME tv /\
    value_has_type tv (StructV fields) ==>
    LENGTH
      (enc_tuple (head_lengths (vyper_to_abi_types (tenv \\ type_key nsid) (MAP SND args)) 0) 0
         (vyper_to_abi_types (tenv \\ type_key nsid) (MAP SND args)) avs [] []) <=
    vyper_abi_size_bound tenv (StructT nsid)
Proof
  rpt strip_tac >>
  qpat_x_assum `evaluate_type tenv (StructT nsid) = SOME tv` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> gvs[value_has_type_def, vyper_abi_size_bound_def] >>
  `LENGTH tvs = LENGTH args` by
    (qpat_x_assum `evaluate_types _ _ [] = SOME tvs` mp_tac >>
     simp[evaluate_types_OPT_MMAP] >> strip_tac >>
     imp_res_tac OPT_MMAP_LENGTH >> simp[LENGTH_MAP]) >>
  `values_have_types tvs (MAP SND fields)` by
    (drule_all struct_has_type_values_have_types >> simp[MAP_ZIP]) >>
  `abi_av_list_bound_rel (tenv \\ type_key nsid) (MAP SND args) avs tvs` by
    (qpat_x_assum `!tvs. _ ==> abi_av_list_bound_rel _ _ _ _`
       (qspec_then `tvs` irule) >>
     simp[] >> irule evaluate_types_LIST_REL >> simp[]) >>
  drule_all abi_av_list_tuple_bound_enc_tuple >> simp[]
QED

Theorem abi_avs_dyn_array_bound[local]:
  !tenv typ tv avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH avs * vyper_abi_embedded_size tenv typ
Proof
  rpt strip_tac >>
  irule enc_dyn_array_same_length_bound_static_premise >>
  conj_tac
  >- (qexists `vyper_abi_size_bound tenv typ` >> rpt conj_tac
      >- (rpt strip_tac >> gvs[EVERY_MEM, abi_av_bound_rel_def] >>
          first_x_assum drule >> simp[abi_av_bound_rel_def]) >>
      drule_all vyper_to_abi_embedded_head_bound >> simp[]) >>
  strip_tac >> rpt strip_tac >>
  gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  drule_all abi_av_bound_rel_static_premise >> simp[]
QED

Theorem abi_avs_fixed_array_bound[local]:
  !tenv typ tv n avs.
    evaluate_type tenv typ = SOME tv /\
    EVERY (abi_av_bound_rel tenv typ tv) avs /\
    LENGTH avs <= n ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ
Proof
  rpt strip_tac >>
  irule enc_fixed_array_same_length_bound_static_premise >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qexists `vyper_abi_size_bound tenv typ` >> rpt conj_tac
      >- (rpt strip_tac >> gvs[EVERY_MEM, abi_av_bound_rel_def] >>
          first_x_assum drule >> simp[abi_av_bound_rel_def]) >>
      drule_all vyper_to_abi_embedded_head_bound >> simp[]) >>
  strip_tac >> rpt strip_tac >>
  gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  drule_all abi_av_bound_rel_static_premise >> simp[]
QED

Theorem abi_avs_dyn_array_bound_from_eval_vht[local]:
  !tenv typ bd vs avs tv.
    (!tv'.
       evaluate_type tenv typ = SOME tv' /\ all_have_type tv' vs ==>
       EVERY (abi_av_bound_rel tenv typ tv') avs /\ LENGTH avs = LENGTH vs) /\
    evaluate_type tenv (ArrayT typ bd) = SOME tv /\
    value_has_type tv (ArrayV (DynArrayV vs)) ==>
    LENGTH (enc (vyper_to_abi_type tenv (ArrayT typ bd)) (ListV avs)) <=
    vyper_abi_size_bound tenv (ArrayT typ bd)
Proof
  rpt strip_tac >>
  qpat_x_assum `evaluate_type tenv (ArrayT typ bd) = SOME tv` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> Cases_on `bd` >>
  gvs[value_has_type_def, vyper_to_abi_type_def, vyper_abi_size_bound_def] >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
   32 + LENGTH avs * vyper_abi_embedded_size tenv typ` by
    (irule abi_avs_dyn_array_bound >> simp[]) >>
  pop_assum mp_tac >>
  simp[Once contractABITheory.enc_def, vyper_abi_size_bound_def] >>
  qabbrev_tac `emb = if vyper_is_dynamic tenv typ then
                        vyper_abi_size_bound tenv typ + 32
                      else vyper_abi_size_bound tenv typ` >>
  `emb * LENGTH vs <= emb * n` by
    (simp[MULT_COMM] >> irule LESS_MONO_MULT >> simp[]) >>
  decide_tac
QED


Theorem sparse_has_type_values_have_type[local]:
  !tv n sparse.
    sparse_has_type tv n sparse ==> sparse_values_have_type tv sparse
Proof
  rpt gen_tac >> Induct_on `sparse` >>
  simp[value_has_type_def, sparse_values_have_type_def] >>
  Cases_on `h` >> simp[value_has_type_def, sparse_values_have_type_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `sparse_values_have_type tv sparse` mp_tac >>
  simp[sparse_values_have_type_def] >> metis_tac[]
QED
Theorem abi_avs_fixed_array_bound_from_eval_vht[local]:
  !tenv typ n sparse avs tv tv'.
    (sparse_values_have_type tv' sparse ==>
       EVERY (abi_av_bound_rel tenv typ tv') avs /\ LENGTH avs = n) /\
    evaluate_type tenv typ = SOME tv' /\
    evaluate_type tenv (ArrayT typ (Fixed n)) = SOME tv /\
    value_has_type tv (ArrayV (SArrayV sparse)) ==>
    LENGTH
      (enc_tuple (head_lengths (REPLICATE (LENGTH avs) (vyper_to_abi_type tenv typ)) 0) 0
         (REPLICATE (LENGTH avs) (vyper_to_abi_type tenv typ)) avs [] []) <=
    vyper_abi_size_bound tenv (ArrayT typ (Fixed n))
Proof
  rpt strip_tac >>
  qpat_x_assum `evaluate_type tenv (ArrayT typ (Fixed n)) = SOME tv` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), LET_THM] >>
  strip_tac >> gvs[value_has_type_def] >>
  drule sparse_has_type_values_have_type >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[vyper_abi_size_bound_def] >>
  qspecl_then [`tenv`, `typ`, `tv'`, `LENGTH avs`, `avs`] mp_tac
    abi_avs_fixed_array_bound >>
  simp[Once contractABITheory.enc_def, vyper_to_abi_type_def,
       vyper_abi_size_bound_def]
QED


Theorem sparse_values_have_type_ALOOKUP[local]:
  !tv sparse k v.
    sparse_values_have_type tv sparse /\ ALOOKUP sparse k = SOME v ==>
    value_has_type tv v
Proof
  rpt gen_tac >> Induct_on `sparse` >> simp[] >>
  Cases_on `h` >> simp[sparse_values_have_type_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `q = k` >> gvs[] >>
  qpat_x_assum `sparse_values_have_type tv sparse ==> value_has_type tv v` irule >>
  simp[sparse_values_have_type_def] >> metis_tac[]
QED

Theorem vyper_to_abi_bound_rel_strong[local]:
  (!tenv typ v av tv.
     vyper_to_abi tenv typ v = SOME av /\
     evaluate_type tenv typ = SOME tv /\
     value_has_type tv v ==>
     abi_av_bound_rel tenv typ tv av) /\
  (!tenv ts vs avs tvs.
     vyper_to_abi_list tenv ts vs = SOME avs /\
     LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
     values_have_types tvs vs ==>
     abi_av_list_bound_rel tenv ts avs tvs) /\
  (!tenv typ vs avs tv.
     vyper_to_abi_same tenv typ vs = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     all_have_type tv vs ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = LENGTH vs) /\
  (!tenv typ tv n sparse avs.
     vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
     evaluate_type tenv typ = SOME tv /\
     sparse_values_have_type tv sparse ==>
     EVERY (abi_av_bound_rel tenv typ tv) avs /\ LENGTH avs = n)
Proof
  ho_match_mp_tac vyper_to_abi_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[vyper_to_abi_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  gvs[abi_av_bound_rel_def, abi_av_list_bound_rel_def,
      value_has_type_def, AllCaseEqs(), LET_THM] >>
  TRY (drule_all vyper_to_abi_base_enc_length_bound >> simp[] >> NO_TAC) >>
  TRY (drule_all abi_av_list_tuple_bound_from_eval_vht >> simp[] >> NO_TAC) >>
  TRY (drule_all abi_av_list_struct_bound_from_eval_vht >> simp[] >> NO_TAC) >>
  TRY (drule_all abi_avs_dyn_array_bound_from_eval_vht >> simp[] >> NO_TAC) >>
  TRY (drule_all abi_avs_fixed_array_bound_from_eval_vht >> simp[] >> NO_TAC) >>
  TRY (drule_all default_to_abi_enc_length_bound >> simp[] >> NO_TAC) >>
  TRY (drule_all sparse_values_have_type_ALOOKUP >> strip_tac >>
       qpat_x_assum `value_has_type _ _ ==> _` drule >> simp[] >> NO_TAC) >>
  TRY (irule abi_av_list_tuple_bound_enc_tuple >> simp[vyper_abi_size_bound_def] >> NO_TAC) >>
  TRY (irule abi_av_list_tuple_bound >> simp[vyper_abi_size_bound_def] >> NO_TAC) >>
  TRY (irule abi_avs_dyn_array_bound >> simp[] >> NO_TAC) >>
  TRY (irule abi_avs_fixed_array_bound >> simp[] >> NO_TAC) >>
  TRY (simp[Once contractABITheory.enc_def, REV_DEF, LENGTH_FLAT,
            vyper_abi_size_bound_def] >> NO_TAC) >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  FAIL_TAC "probe_c4454_strong"
QED


Theorem vyper_to_abi_enc_length_bound:
  (!tenv typ v av tv.
    vyper_to_abi tenv typ v = SOME av /\
    evaluate_type tenv typ = SOME tv /\
    value_has_type tv v ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    vyper_abi_size_bound tenv typ) /\
  (!tenv ts vs avs tvs.
    vyper_to_abi_list tenv ts vs = SOME avs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs /\
    values_have_types tvs vs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound_list tenv ts) /\
  (!tenv typ vs avs tv.
    vyper_to_abi_same tenv typ vs = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    all_have_type tv vs ==>
    LENGTH (enc (Array NONE (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    32 + LENGTH vs * vyper_abi_embedded_size tenv typ) /\
  (!tenv typ tv n sparse avs.
    vyper_to_abi_sparse tenv typ tv n sparse = SOME avs /\
    evaluate_type tenv typ = SOME tv /\
    sparse_has_type tv n sparse ==>
    LENGTH (enc (Array (SOME n) (vyper_to_abi_type tenv typ)) (ListV avs)) <=
    n * vyper_abi_embedded_size tenv typ)
Proof
  rpt conj_tac
  >- (rpt strip_tac >>
      drule_all (cj 1 vyper_to_abi_bound_rel_strong) >>
      simp[abi_av_bound_rel_def])
  >- (rpt strip_tac >>
      drule_all (cj 2 vyper_to_abi_bound_rel_strong) >> strip_tac >>
      drule_all abi_av_list_tuple_bound >> simp[])
  >- (rpt strip_tac >>
      drule_all (cj 3 vyper_to_abi_bound_rel_strong) >> strip_tac >>
      drule_all abi_avs_dyn_array_bound >> simp[])
  >> rpt strip_tac >>
  drule sparse_has_type_values_have_type >> strip_tac >>
  drule_all (cj 4 vyper_to_abi_bound_rel_strong) >> strip_tac >>
  irule abi_avs_fixed_array_bound >> simp[]
QED

(* TODO: AbiEncode result typing needs a static encoded-size bound in the type system. *)
