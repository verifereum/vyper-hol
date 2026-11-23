Theory whitelistNestedTypeProps
Ancestors
  arithmetic finite_map list pair pred_set vyperAST vyperImportRefs
  vyperTypeSystem whitelistCheckerTypes supportedTypes

Theorem imported_types_refs_ok_every[local]:
  !tys. imported_types_refs_ok tys <=> EVERY imported_type_refs_ok tys
Proof
  Induct >> simp[imported_type_refs_ok_def]
QED

Theorem linked_nested_with_fuel:
  !tenv ty. assignable_type tenv ty ==>
    !(R : nsid set) fuel tops leaf.
      FINITE R /\ CARD R <= fuel /\
      (!t. supported_scalar_type t ==> leaf t) /\
      (imported_type_refs_ok ty \/
       (!s fs. FLOOKUP tenv (NONE,s) = SOME (StructArgs fs) ==>
               (NONE,s) IN R /\ supported_struct_fields tops (NONE,s) = SOME fs)) ==>
      supported_nested_type leaf fuel tops ty
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`BaseT bt`]
  >- (rw[assignable_type_def, Once supported_nested_type_def] >>
      first_x_assum irule >>
      drule well_formed_base_scalar >>
      rw[supported_scalar_type_def, supported_word_type_def] >>
      gvs[supported_word_type_def])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      fs[assignable_type_def, imported_type_refs_ok_def,
         imported_types_refs_ok_every, EVERY_MEM] >>
      once_rewrite_tac[supported_nested_type_def] >>
      disj2_tac >> simp[EVERY_MEM, NULL_EQ] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[])
  >~ [`ArrayT elem bd`]
  >- (rpt strip_tac >> fs[assignable_type_def, imported_type_refs_ok_def] >>
      `supported_nested_type leaf fuel tops elem` by
        (first_x_assum irule >> metis_tac[]) >>
      once_rewrite_tac[supported_nested_type_def] >>
      Cases_on `bd` >> simp[] >>
      metis_tac[well_formed_fixed_array_nonempty])
  >~ [`StructT id`]
  >- (rpt gen_tac >> Cases_on `FST id = NONE` >> rpt strip_tac >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      gvs[imported_type_refs_ok_def] >>
      PairCases_on `id` >> gvs[] >> rename1 `StructT (NONE,s)` >>
      Cases_on `FLOOKUP tenv (NONE,s)` >> fs[assignable_type_def] >>
      rename1 `FLOOKUP tenv (NONE,s) = SOME desc` >>
      Cases_on `desc` >> fs[] >>
      rename1 `FLOOKUP tenv (NONE,s) = SOME (StructArgs args)` >>
      qpat_assum `!s fs. FLOOKUP tenv (NONE,s) = SOME (StructArgs fs) ==> _`
        drule >> strip_tac >>
      `CARD R <> 0` by (strip_tac >> gvs[CARD_EQ_0]) >>
      `fuel <> 0` by decide_tac >>
      `CARD (R DELETE (NONE,s)) <= fuel - 1` by
        (simp[CARD_DELETE] >> decide_tac) >>
      disj2_tac >> simp[EVERY_MEM, NULL_EQ] >> rpt strip_tac >>
      fs[EVERY_MEM] >> first_x_assum irule >> simp[] >>
      qexists `R DELETE (NONE,s)` >> simp[] >>
      disj2_tac >> rw[DOMSUB_FLOOKUP_THM, AllCaseEqs()] >> metis_tac[])
  >~ [`FlagT id`]
  >- (rw[Once supported_nested_type_def] >>
      first_x_assum irule >> simp[supported_scalar_type_def])
  >> simp[assignable_type_def]
QED
