(* Finite named-struct support saturates within the declaration count. *)
Theory bodyIntCallFamAggAttributeSaturation
Ancestors
  bodyIntCallFamAggAttributeSupport supportedTypes vyperAST list arithmetic pred_set

Theorem supported_struct_fields_domain_cover:
  !tops id fs. supported_struct_fields tops id = SOME fs ==>
    MEM id (MAP (\top. case top of StructDecl s fields => (NONE,s)
                                 | _ => (NONE,"")) tops)
Proof
  Induct >> simp[supported_struct_fields_def] >>
  Cases_on `id` >> Cases_on `h` >>
  simp[supported_struct_fields_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supported_struct_fields_domain_bound:
  FINITE {id | ?fs. supported_struct_fields tops id = SOME fs} /\
  CARD {id | ?fs. supported_struct_fields tops id = SOME fs} <= LENGTH tops
Proof
  qmatch_goalsub_abbrev_tac `FINITE D` >>
  qabbrev_tac `xs : nsid list = MAP (\top. case top of StructDecl s fields => (NONE,s)
                                       | _ => (NONE,"")) tops` >>
  `D SUBSET set xs` by
    (simp[Abbr `D`, Abbr `xs`, SUBSET_DEF] >>
     metis_tac[supported_struct_fields_domain_cover]) >>
  `FINITE D` by metis_tac[SUBSET_FINITE, FINITE_LIST_TO_SET] >>
  simp[] >>
  `CARD D <= CARD (set xs)` by metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  `CARD (set xs) <= LENGTH xs` by simp[CARD_LIST_TO_SET] >>
  gvs[Abbr `xs`]
QED

Theorem finite_strict_chain_growth:
  !n S. (!i. i <= n ==> FINITE (S i)) /\
        (!i. i < n ==> S i PSUBSET S (SUC i)) ==>
        n <= CARD (S n)
Proof
  Induct >- simp[] >> qx_gen_tac `ss` >> strip_tac >>
  `n <= CARD (ss n)` by (first_x_assum irule >> simp[]) >>
  `ss n PSUBSET ss (SUC n)` by simp[] >>
  `FINITE (ss (SUC n))` by simp[] >>
  drule_all CARD_PSUBSET >> decide_tac
QED

Theorem finite_chain_adjacent_eq:
  !D ss. FINITE D /\ (!i. ss i SUBSET D) /\
  (!i. ss i SUBSET ss (SUC i)) ==>
  ?i. i <= CARD D /\ ss i = ss (SUC i)
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `!i. i < SUC (CARD D) ==> ss i PSUBSET ss (SUC i)` by
    (simp[PSUBSET_DEF] >> metis_tac[LESS_EQ_IFF_LESS_SUC]) >>
  `!i. FINITE (ss i)` by metis_tac[SUBSET_FINITE] >>
  `SUC (CARD D) <= CARD (ss (SUC (CARD D)))` by
    (irule finite_strict_chain_growth >> simp[]) >>
  `CARD (ss (SUC (CARD D))) <= CARD D` by metis_tac[CARD_SUBSET] >>
  decide_tac
QED

Theorem supported_nested_type_adjacent_eq:
  !leaf tops. ?i. i <= LENGTH tops /\
    !ty. supported_nested_type leaf i tops ty <=>
         supported_nested_type leaf (SUC i) tops ty
Proof
  rpt gen_tac >>
  qabbrev_tac `D = {id | ?fs. supported_struct_fields tops id = SOME fs}` >>
  qabbrev_tac `ss = \i. {id | id IN D /\
    supported_nested_type leaf i tops (StructT id)}` >>
  `FINITE D /\ CARD D <= LENGTH tops` by
    simp[Abbr `D`, supported_struct_fields_domain_bound] >>
  `!i. ss i SUBSET D` by simp[Abbr `ss`, SUBSET_DEF] >>
  `!i. ss i SUBSET ss (SUC i)` by
    (simp[Abbr `ss`, SUBSET_DEF] >>
     metis_tac[supported_nested_type_mono, LESS_EQ_SUC_REFL]) >>
  drule_all finite_chain_adjacent_eq >> strip_tac >>
  qexists `i` >> conj_tac >- decide_tac >>
  irule supported_nested_type_struct_agree >> gen_tac >>
  Cases_on `id IN D`
  >- (qpat_x_assum `ss i = _` mp_tac >>
      simp[Abbr `ss`, EXTENSION] >> metis_tac[]) >>
  `supported_struct_fields tops id = NONE` by
    (gvs[Abbr `D`] >> Cases_on `supported_struct_fields tops id` >> gvs[]) >>
  once_rewrite_tac[supported_nested_type_def] >> simp[]
QED

Theorem supported_nested_type_saturated:
  !leaf fuel tops ty. supported_nested_type leaf fuel tops ty ==>
    supported_nested_type leaf (LENGTH tops) tops ty
Proof
  rpt strip_tac >>
  qspecl_then [`leaf`, `tops`] strip_assume_tac supported_nested_type_adjacent_eq >>
  Cases_on `fuel <= LENGTH tops`
  >- metis_tac[supported_nested_type_mono] >>
  drule supported_nested_type_stable >> strip_tac >>
  `fuel = i + (fuel - i)` by decide_tac >>
  `LENGTH tops = i + (LENGTH tops - i)` by decide_tac >>
  metis_tac[]
QED
