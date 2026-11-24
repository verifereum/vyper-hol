(* Pure support for the closed constant fragment of a checked linked unit. *)
Theory whitelistLinkedConstFragment
Ancestors
  constSubstCorrect vyperTypeConstantCells vyperTypeConstantFold
  vyperTypeContractStaticMaps vyperTypeContract vyperTypeSystem vyperImportRefs
  vyperAST vyperContext vyperValue exprLowering
  whitelistLinkedExprFormProps whitelistCheckerExprs whitelistCheckerTypes supportedExprs supportedExprForms
  supportedTypes supportedGetterProps finite_map alist list pair option
  whitelistStructFieldProps

(* The constant typing lemmas are phrased for a context containing the unit.
   Only the source-table lookup is used here. *)
Triviality const_unit_context:
  ?cx. ALOOKUP cx.sources cx.txn.target = SOME mods
Proof
  qexists_tac `empty_evaluation_context with sources :=
                 [(empty_evaluation_context.txn.target,mods)]` >> simp[]
QED

Triviality const_name_assignable:
  check_contract F layouts addr mods = SOME art /\
  declared_constant mods owner id /\
  well_typed_expr (artifact_env art mods src) (TopLevelName ty (owner,id)) ==>
  assignable_type (type_env_all_modules mods) ty
Proof
  strip_tac >> fs[declared_constant_def] >>
  drule check_contract_runtime_namespaces >> strip_tac >>
  `ALOOKUP mods owner = SOME tls` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  drule_all checked_const_decl_typed >> strip_tac >>
  `?cx. ALOOKUP cx.sources cx.txn.target = SOME mods` by simp[const_unit_context] >>
  drule_all checked_constant_declared_type >> simp[]
QED

Triviality closed_typed_const_supported_mutual:
  check_contract F layouts addr mods = SOME art /\
  (!ty. assignable_type (type_env_all_modules mods) ty /\
        (src <> NONE ==> imported_type_refs_ok ty) ==>
        supported_place_type tops ty) /\
  (!k fs. FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs fs) ==>
          EVERY (assignable_type (type_env_all_modules mods) o SND) fs /\
          (well_formed_type (type_env_all_modules mods) (StructT k) ==>
           assignable_type (type_env_all_modules mods) (StructT k)) /\
          (src = NONE /\ FST k = NONE ==> supported_struct_fields tops k = SOME fs)) /\
  (!b. constant_expr mods b /\ const_local_refs b = [] ==>
       (qualified_place_root b \/ supported_place_info tops b = ValPT (expr_type b)) /\
       (supported_pure_expr tops b ==> supported_place_expr tops b)) ==>
  (!e. constant_expr mods e /\ const_local_refs e = [] /\
       well_typed_expr (artifact_env art mods src) e /\
       (src <> NONE ==> imported_expr_refs_ok e) ==>
       supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e)) /\
  (!es. EVERY (constant_expr mods) es /\ const_local_exprs es = [] /\
        well_typed_exprs (artifact_env art mods src) es /\
        (src <> NONE ==> imported_exprs_refs_ok es) ==>
        supported_pure_exprs tops es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ const_local_fields fs = [] /\
        well_typed_named_exprs (artifact_env art mods src) fs /\
        (src <> NONE ==> imported_field_refs_ok fs) ==>
        supported_pure_fields tops fs)
Proof
  strip_tac >>
  (* Retain aggregate support while traversing the builtin argument list. *)
  `(!e. constant_expr mods e /\ const_local_refs e = [] /\
        well_typed_expr (artifact_env art mods src) e /\
        (src <> NONE ==> imported_expr_refs_ok e) ==>
        supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e)) /\
   (!es. EVERY (constant_expr mods) es /\ const_local_exprs es = [] /\
         well_typed_exprs (artifact_env art mods src) es /\
         (src <> NONE ==> imported_exprs_refs_ok es) ==>
         supported_pure_exprs tops es /\
         EVERY (\e. checker_agg_ok tops (expr_type e)) es) /\
   (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ const_local_fields fs = [] /\
         well_typed_named_exprs (artifact_env art mods src) fs /\
         (src <> NONE ==> imported_field_refs_ok fs) ==>
         supported_pure_fields tops fs)` suffices_by metis_tac[] >>
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, const_local_refs_def, imported_expr_refs_ok_def,
       expr_type_def, SF ETA_ss] >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  >~ [`supported_pure_expr _ (TopLevelName _ _)`] >-
    (rename1 `TopLevelName ty k` >> PairCases_on `k` >> Cases_on `k0` >>
     gvs[const_local_refs_def, constant_expr_def] >>
     drule_all const_name_assignable >> strip_tac >>
     `supported_place_type tops ty` by metis_tac[] >>
     fs[supported_pure_expr_def, supported_storage_value_def,
        supported_storage_type_def, supported_place_type_def, checker_agg_ok_def])
  >~ [`supported_pure_expr _ (Literal _ _)`] >-
    (gvs[well_typed_expr_def, supported_pure_expr_def] >>
     rename1 `well_typed_literal ty lit` >> Cases_on `ty` >>
     simp[checker_agg_ok_def] >> Cases_on `lit` >> gvs[well_typed_literal_def])
  >~ [`supported_pure_expr _ (StructLit _ _ _)`] >-
    (gvs[well_typed_expr_def, artifact_env_def, supported_pure_expr_def,
         checker_agg_ok_def, supported_struct_elements_def] >>
     qpat_x_assum `!k fs. FLOOKUP _ _ = _ ==> _` drule >> strip_tac >>
     `supported_place_type tops (StructT ns)` by
       (first_x_assum irule >> gvs[imported_type_refs_ok_def]) >>
     simp[] >> disch_tac >>
     `src = NONE` by metis_tac[] >> gvs[structlit_fields_lookup])
  >~ [`supported_pure_expr _ (Subscript _ _ _)`] >-
    (rename1 `Subscript ty b ix` >>
     `?cx. ALOOKUP cx.sources cx.txn.target = SOME mods` by simp[const_unit_context] >>
     drule_all constant_subscript_base_well_typed >> strip_tac >>
     drule_all constant_subscript_type_ok >> strip_tac >>
     `well_typed_expr (artifact_env art mods src) ix` by fs[Once well_typed_expr_def] >>
     `supported_pure_expr tops ix` by metis_tac[] >>
     `supported_pure_expr tops b /\ checker_agg_ok tops (expr_type b)` by metis_tac[] >>
     `supported_place_expr tops b /\
      (~qualified_place_root b ==> supported_place_info tops b = ValPT (expr_type b))`
       by metis_tac[] >>
     `supported_subscript_place tops b /\ supported_place_type tops ty` by
       (irule linked_subscript_value >> simp[] >> qexists_tac `ix` >> simp[]) >>
     simp[supported_pure_expr_def, checker_agg_ok_def])
  >~ [`supported_pure_expr _ (Attribute _ _ _)`] >-
    (rename1 `Attribute ty b f` >> gvs[well_typed_expr_def, artifact_env_def] >>
     `supported_pure_expr tops b` by metis_tac[] >>
     `supported_place_expr tops b` by metis_tac[] >>
     `src <> NONE ==> imported_type_refs_ok (expr_type b)` by
       metis_tac[imported_expr_refs_type] >>
     Cases_on `expr_type b` >>
     gvs[attribute_type_ok_def, attribute_type_def, AllCaseEqs()] >>
     rename1 `FLOOKUP _ k = SOME (StructArgs fs)` >>
     qpat_x_assum `!k fs. FLOOKUP _ _ = _ ==> _` drule >> strip_tac >>
     `assignable_type (type_env_all_modules mods) ty` by
       (drule_then assume_tac ALOOKUP_MEM >>
        qpat_x_assum `EVERY _ fs` mp_tac >> simp[EVERY_MEM] >>
        disch_then drule >> simp[]) >>
     `supported_place_type tops ty` by metis_tac[] >>
     simp[supported_pure_expr_def, checker_agg_ok_def, supported_field_place_def] >>
     Cases_on `FST k = NONE` >> gvs[imported_type_refs_ok_def] >>
     drule ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[])
  >~ [`supported_pure_expr _ (Builtin _ _ _)`] >-
    (rename1 `Builtin ty bt es` >>
     gvs[well_typed_expr_def, artifact_env_def, supported_pure_expr_def] >>
     `supported_pure_exprs tops es /\ EVERY (\e. checker_agg_ok tops (expr_type e)) es`
       by metis_tac[] >>
     simp[] >> irule linked_builtin_form >> simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[])
     >> strip_tac >> gvs[well_typed_builtin_app_def, MAP_EQ_CONS])
  >~ [`supported_pure_expr _ (TypeBuiltin _ _ _ _)`] >-
    (rename1 `TypeBuiltin ty tb target es` >>
     gvs[well_typed_expr_def, artifact_env_def, supported_pure_expr_def] >>
     `supported_pure_exprs tops es` by metis_tac[] >> simp[] >>
     `src <> NONE ==> imported_type_refs_ok ty` by
       metis_tac[imported_expr_refs_type, expr_type_def] >>
     irule linked_type_builtin_form >> simp[] >>
     qexists_tac `type_env_all_modules mods` >> simp[] >> metis_tac[])
  >> gvs[well_typed_expr_def, supported_pure_expr_def] >> metis_tac[]
QED

Theorem closed_typed_const_supported:
  check_contract F layouts addr mods = SOME art /\
  (!ty. assignable_type (type_env_all_modules mods) ty /\
        (src <> NONE ==> imported_type_refs_ok ty) ==>
        supported_place_type tops ty) /\
  (!k fs. FLOOKUP (type_env_all_modules mods) k = SOME (StructArgs fs) ==>
          EVERY (assignable_type (type_env_all_modules mods) o SND) fs /\
          (well_formed_type (type_env_all_modules mods) (StructT k) ==>
           assignable_type (type_env_all_modules mods) (StructT k)) /\
          (src = NONE /\ FST k = NONE ==> supported_struct_fields tops k = SOME fs)) /\
  (!b. constant_expr mods b /\ const_local_refs b = [] ==>
       (qualified_place_root b \/ supported_place_info tops b = ValPT (expr_type b)) /\
       (supported_pure_expr tops b ==> supported_place_expr tops b)) ==>
  !e. constant_expr mods e /\ const_local_refs e = [] /\
      well_typed_expr (artifact_env art mods src) e /\
      (src <> NONE ==> imported_expr_refs_ok e) ==>
      supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e)
Proof
  strip_tac >> drule_all closed_typed_const_supported_mutual >> simp[]
QED
