(* Type support in a linked environment. Only unqualified struct references
   expand fields in the whitelist, so only they draw on the module's fuel. *)
Theory whitelistLinkedTypeSupport
Ancestors
  arithmetic list pair pred_set finite_map alist vyperAST vyperContext
  vyperImportRefs vyperTypeSystem vyperTypeContract
  vyperTypeConstantFold whitelistCheckerExprs whitelistCheckerTypes
  supportedTypes whitelistNestedTypeProps whitelistHashmapValueProps

Theorem linked_assignable_type_supported_nested:
  ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods src = SOME tops /\
  assignable_type (type_env_all_modules mods) ty /\
  (src <> NONE ==> imported_type_refs_ok ty) /\
  (!t. supported_scalar_type t ==> leaf t) ==>
  supported_nested_type leaf (LENGTH tops) tops ty
Proof
  strip_tac >> drule linked_nested_with_fuel >> disch_then irule >> simp[] >>
  qexists `FDOM (type_env tops)` >>
  simp[type_env_def, type_env_card_le] >>
  Cases_on `src` >> gvs[] >> disj2_tac >>
  simp[FLOOKUP_type_env_all_modules] >> rpt strip_tac
  >- gvs[flookup_thm]
  >> irule type_env_struct_fields >> simp[type_env_def]
QED

Theorem linked_assignable_type_supported_place:
  ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods src = SOME tops /\
  assignable_type (type_env_all_modules mods) ty /\
  (src <> NONE ==> imported_type_refs_ok ty) ==>
  supported_place_type tops ty
Proof
  simp[supported_place_type_def] >>
  strip_tac >> irule linked_assignable_type_supported_nested >>
  simp[] >> metis_tac[]
QED

Theorem linked_check_value_type_supported_hashmap_value:
  ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods src = SOME tops /\
  check_value_type (type_env_all_modules mods) vt /\
  (src <> NONE ==> imported_value_type_refs_ok vt) ==>
  supported_hashmap_value tops vt
Proof
  strip_tac >>
  mp_tac (Q.INST [`tenv` |-> `type_env_all_modules mods`,
                  `imported_only` |-> `(src:num option) <> NONE`]
    checked_hashmap_value_supported) >>
  impl_tac >- metis_tac[linked_assignable_type_supported_place, checker_hashmap_key_supported] >>
  disch_then (qspec_then `vt` mp_tac) >> simp[]
QED
