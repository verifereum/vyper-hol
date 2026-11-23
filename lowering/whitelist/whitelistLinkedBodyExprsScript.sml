Theory whitelistLinkedBodyExprs
Ancestors
  whitelistLinkedBodyEnv whitelistLinkedExprFormProps whitelistCheckerExprs whitelistCheckerTypes
  supportedPlaceAssignable typedCopyMetadata vyperImportRefs vyperTypeArgFits
  vyperAST vyperTypeSystem vyperTypeContract vyperValue supportedExprs supportedExprForms
  supportedTypes supportedDecls supportedGetterProps exprLowering compileEnv
  list rich_list alist
  finite_map pair
  whitelistExprTypeProps whitelistStructFieldProps

Theorem linked_expr_place_type[local]:
  linked_body_env tops src tenv env /\ assignable_type env.type_defs ty /\
  (src = NONE \/ imported_type_refs_ok ty) ==>
  supported_place_type tops ty
Proof
  simp[linked_body_env_def, linked_body_type_facts_def] >> metis_tac[]
QED

(* A qualified path does not use the module-local compiler descriptor. *)
Theorem linked_place_info_subscript[local]:
  (~qualified_place_root be ==>
   supported_place_info tops be = value_type_place vt) /\
  subscript_vtype vt kty = SOME vt' /\ vtype_annotation_ok vt' ty ==>
  (~qualified_place_root (Subscript ty be key) ==>
   supported_place_info tops (Subscript ty be key) = value_type_place vt')
Proof
  simp[qualified_place_root_def, supported_place_info_def] >> strip_tac >>
  Cases_on `vt` >> gvs[place_type_def, value_type_place_def, subscript_vtype_def] >>
  rename1 `subscript_vtype (Type t)` >> Cases_on `t` >>
  gvs[subscript_vtype_def, AllCaseEqs(), value_type_place_def, vtype_annotation_ok_def]
QED

Theorem linked_subscript_place[local]:
  linked_body_type_facts tops src tenv /\ check_value_type tenv vt /\
  subscript_vtype vt kty = SOME vt' /\
  (~qualified_place_root e ==>
   src = NONE /\ supported_place_info tops e = value_type_place vt) ==>
  supported_subscript_place tops e /\ check_value_type tenv vt'
Proof
  strip_tac >> conj_tac
  >- (Cases_on `qualified_place_root e` >> gvs[supported_subscript_place_def] >>
      Cases_on `vt`
      >- (rename1 `subscript_vtype (Type t)` >> Cases_on `t` >>
          gvs[subscript_vtype_def, check_value_type_def, value_type_place_def,
              linked_body_type_facts_def] >> metis_tac[check_value_type_def]) >>
      gvs[value_type_place_def] >>
      `!ty. assignable_type tenv ty ==> supported_place_type tops ty` by
        fs[linked_body_type_facts_def] >>
      drule_all checked_value_type_supported_hashmap >> simp[supported_hashmap_value_def]) >>
  metis_tac[check_value_type_subscript_child]
QED

Theorem linked_structlit_form[local]:
  linked_body_type_facts tops src tenv /\
  (src = NONE \/ FST k <> NONE) /\
  well_formed_type tenv (StructT k) /\ FLOOKUP tenv k = SOME (StructArgs fields) /\
  MAP FST es = MAP FST fields ==>
  supported_struct_elements tops (StructT k) es
Proof
  strip_tac >> Cases_on `k` >> rename1 `FLOOKUP tenv (ns,name) = _` >>
  Cases_on `ns` >>
  gvs[supported_struct_elements_def]
  >- (gvs[linked_body_type_facts_def] >>
      `supported_struct_fields tops (NONE,name) = SOME fields` by
        (qpat_assum `!k fs. _ ==> supported_struct_fields _ _ = _` $
           qspecl_then [`(NONE,name)`, `fields`] mp_tac >> simp[]) >>
      simp[structlit_fields_lookup]) >>
  simp[supported_place_type_def, Once supported_nested_type_def]
QED

Theorem linked_attribute_field[local]:
  linked_body_type_facts tops src tenv /\
  (src = NONE \/ imported_type_refs_ok be) /\
  attribute_type_ok tenv be fld ty ==>
  supported_field_place tops be fld /\ assignable_type tenv ty
Proof
  Cases_on `be` >>
  simp[attribute_type_ok_def, attribute_type_def, supported_field_place_def,
       imported_type_refs_ok_def, linked_body_type_facts_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
  gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
  TRY (qpat_assum `!k fs. _ ==> supported_struct_fields _ _ = _` drule_all >>
       disch_then (fn th => simp[th]) >> qexists `ty` >> simp[] >> NO_TAC) >>
  metis_tac[SND]
QED

Theorem linked_place_root_info[local]:
  linked_body_data_env tops src env /\ (src = NONE \/ FST k <> NONE) /\
  FLOOKUP env.toplevel_vtypes k = SOME vt /\ vtype_annotation_ok vt ty ==>
  supported_place_root tops k /\ check_value_type env.type_defs vt /\
  (FST k = NONE ==>
   src = NONE /\ supported_place_info tops (TopLevelName ty k) = value_type_place vt)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then strip_assume_tac linked_body_toplevel_place >> simp[] >>
  strip_tac >> `src = NONE` by metis_tac[] >>
  fs[linked_body_data_env_def] >>
  qpat_assum `!k vt. _ ==> supported_place_root _ _ /\ _` drule_all >>
  Cases_on `vt` >>
  simp[supported_place_info_def, place_type_def, value_type_place_def,
       vtype_annotation_ok_def] >> strip_tac >> gvs[vtype_annotation_ok_def]
QED

Theorem linked_value_root_info[local]:
  linked_body_data_env tops src env /\ (src = NONE \/ FST k <> NONE) /\
  (FLOOKUP env.toplevel_vtypes k = SOME (Type ty) \/
   FLOOKUP env.bare_globals k = SOME ty) ==>
  supported_place_root tops k /\
  (FST k = NONE ==> supported_place_info tops (TopLevelName ty k) = ValPT ty)
Proof
  strip_tac >>
  `FLOOKUP env.toplevel_vtypes k = SOME (Type ty)` by
    (fs[linked_body_data_env_def] >> metis_tac[]) >>
  metis_tac[linked_place_root_info, vtype_annotation_ok_def, value_type_place_def]
QED

Theorem linked_internal_call[local]:
  linked_body_env tops src tenv env /\
  (src = NONE \/ FST k <> NONE) /\ (src = NONE \/ imported_type_refs_ok ty) /\
  FLOOKUP env.fn_sigs k = SOME sg /\ type_widens_to env.type_defs sg.ret_ty ty ==>
  (FST k <> NONE \/ IS_SOME (supported_function_decl tops k Internal)) /\
  checker_agg_ok tops ty
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `linked_body_calls_env tops src env` by fs[linked_body_env_def] >>
  reverse conj_tac
  >- (fs[linked_body_calls_env_def] >>
      qpat_assum `!k sg. _ ==> sg.ret_ty = _ \/ _` drule >> strip_tac >>
      gvs[checker_agg_ok_def] >> metis_tac[type_widens_to_assignable_type,
                                         linked_expr_place_type]) >>
  Cases_on `FST k = NONE` >> gvs[linked_body_calls_env_def] >>
  qpat_assum `!id f. _ ==> ?m nr rr args dflts ss. supported_function_decl _ id _ = _` $
    qspecl_then [`k`,`sg`] mp_tac >>
  Cases_on `supported_function_decl tops k Internal` >> simp[]
QED

Theorem linked_toplevel_name_value_supported[local]:
  well_typed_expr env (TopLevelName ty (src_id_opt,id)) ==>
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_expr_refs_ok (TopLevelName ty (src_id_opt,id))) ==>
  supported_pure_expr tops (TopLevelName ty (src_id_opt,id)) /\
  checker_agg_ok tops (expr_type (TopLevelName ty (src_id_opt,id))) /\
  supported_place_expr tops (TopLevelName ty (src_id_opt,id)) /\
  (~qualified_place_root (TopLevelName ty (src_id_opt,id)) ==>
   supported_place_info tops (TopLevelName ty (src_id_opt,id)) = ValPT (expr_type (TopLevelName ty (src_id_opt,id))))
Proof
  simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
       qualified_place_root_def, expr_type_def, LEFT_OR_OVER_AND] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `linked_body_data_env tops src env` by fs[linked_body_env_def] >>
  `supported_place_type tops ty /\
   (supported_storage_value tops (src_id_opt,id) ty \/
    supported_immutable_type tops (src_id_opt,id) = SOME ty \/
    supported_constant_type tops (src_id_opt,id) = SOME ty)` by
    metis_tac[linked_body_value_read, FST] >>
  `supported_place_root tops (src_id_opt,id) /\
   (FST (src_id_opt,id) = NONE ==>
    supported_place_info tops (TopLevelName ty (src_id_opt,id)) = ValPT ty)` by
    metis_tac[linked_value_root_info, FST] >>
  fs[checker_agg_ok_def]
QED

Theorem linked_subscript_value_supported[local]:
  (well_typed_expr env e ==>
   linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e) ==>
   supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e) /\
   supported_place_expr tops e /\
   (~qualified_place_root e ==> supported_place_info tops e = ValPT (expr_type e))) /\
  (well_typed_expr env e' ==>
   linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e') ==>
   supported_pure_expr tops e' /\ checker_agg_ok tops (expr_type e') /\
   supported_place_expr tops e' /\
   (~qualified_place_root e' ==> supported_place_info tops e' = ValPT (expr_type e'))) /\
  (IS_SOME (type_place_expr env e) ==>
    linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e) ==>
    supported_place_expr tops e /\
    check_value_type env.type_defs (THE (type_place_expr env e)) /\
    (~qualified_place_root e ==>
     src = NONE /\ supported_place_info tops e = value_type_place (THE (type_place_expr env e)))) ==>
  well_typed_expr env (Subscript ty e e') ==>
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_expr_refs_ok (Subscript ty e e')) ==>
  supported_pure_expr tops (Subscript ty e e') /\
  checker_agg_ok tops (expr_type (Subscript ty e e')) /\
  supported_place_expr tops (Subscript ty e e') /\
  (~qualified_place_root (Subscript ty e e') ==>
   supported_place_info tops (Subscript ty e e') = ValPT (expr_type (Subscript ty e e')))
Proof
  simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
       expr_type_def, LEFT_OR_OVER_AND] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `(_ /\ subscript_type_ok _ _ _ /\ _) \/ _` strip_assume_tac
  >- (res_tac >> fs[] >> drule_all linked_subscript_value >> strip_tac >>
      simp[checker_agg_ok_def, qualified_place_root_def, supported_place_info_def] >>
      metis_tac[place_type_subscript_value, supported_place_info_def]) >>
  res_tac >> fs[] >>
  `linked_body_type_facts tops src env.type_defs` by fs[linked_body_env_def] >>
  drule_all linked_subscript_place >> strip_tac >>
  `supported_place_type tops ty` by
    metis_tac[check_value_type_def, linked_expr_place_type] >>
  simp[checker_agg_ok_def] >>
  metis_tac[linked_place_info_subscript, vtype_annotation_ok_def, value_type_place_def]
QED

Theorem linked_toplevel_name_place_supported[local]:
  IS_SOME (type_place_expr env (TopLevelName ty (src_id_opt,id))) ==>
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_expr_refs_ok (TopLevelName ty (src_id_opt,id))) ==>
  supported_place_expr tops (TopLevelName ty (src_id_opt,id)) /\
  check_value_type env.type_defs (THE (type_place_expr env (TopLevelName ty (src_id_opt,id)))) /\
  (~qualified_place_root (TopLevelName ty (src_id_opt,id)) ==>
   src = NONE /\
   supported_place_info tops (TopLevelName ty (src_id_opt,id)) =
     value_type_place (THE (type_place_expr env (TopLevelName ty (src_id_opt,id)))))
Proof
  simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
       qualified_place_root_def, LEFT_OR_OVER_AND] >>
  Cases_on `FLOOKUP env.toplevel_vtypes (src_id_opt,id)` >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME vt` >> Cases_on `vtype_annotation_ok vt ty` >> simp[] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `linked_body_data_env tops src env` by fs[linked_body_env_def] >>
  `supported_place_root tops (src_id_opt,id) /\ check_value_type env.type_defs vt /\
   (FST (src_id_opt,id) = NONE ==>
    src = NONE /\ supported_place_info tops (TopLevelName ty (src_id_opt,id)) =
                 value_type_place vt)` by metis_tac[linked_place_root_info, FST] >>
  fs[] >> strip_tac >> gvs[]
QED

Theorem linked_subscript_place_supported[local]:
  (well_typed_expr env e' ==>
   linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e') ==>
   supported_pure_expr tops e' /\ checker_agg_ok tops (expr_type e') /\
   supported_place_expr tops e' /\
   (~qualified_place_root e' ==> supported_place_info tops e' = ValPT (expr_type e'))) /\
  (well_typed_expr env e' ==>
   (IS_SOME (type_place_expr env e) ==>
    linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e) ==>
    supported_place_expr tops e /\
    check_value_type env.type_defs (THE (type_place_expr env e)) /\
    (~qualified_place_root e ==>
     src = NONE /\ supported_place_info tops e = value_type_place (THE (type_place_expr env e))))) ==>
  IS_SOME (type_place_expr env (Subscript ty e e')) ==>
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_expr_refs_ok (Subscript ty e e')) ==>
  supported_place_expr tops (Subscript ty e e') /\
  check_value_type env.type_defs (THE (type_place_expr env (Subscript ty e e'))) /\
  (~qualified_place_root (Subscript ty e e') ==>
   src = NONE /\
   supported_place_info tops (Subscript ty e e') =
     value_type_place (THE (type_place_expr env (Subscript ty e e'))))
Proof
  simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
       LEFT_OR_OVER_AND] >>
  Cases_on `well_typed_expr env e'` >> simp[] >>
  Cases_on `type_place_expr env e` >> simp[] >>
  rename1 `type_place_expr env e = SOME vt` >>
  Cases_on `subscript_vtype vt (expr_type e')` >> simp[] >>
  rename1 `subscript_vtype vt _ = SOME vt'` >>
  Cases_on `vtype_annotation_ok vt' ty` >> simp[] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  res_tac >> fs[] >>
  `linked_body_type_facts tops src env.type_defs` by fs[linked_body_env_def] >>
  drule_all linked_subscript_place >> strip_tac >> simp[] >>
  metis_tac[linked_place_info_subscript, qualified_place_root_def]
QED

(* The expression and place conclusions share their induction: a subscript
   can read a value or continue a storage path. Only unqualified roots need
   their descriptor to agree with the one constructed from tops. *)
Theorem linked_well_typed_expr_supported:
  (src = NONE ==> !name. ~MEM (StructDecl name []) tops) ==>
  (!env e. well_typed_expr env e ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e) ==>
     supported_pure_expr tops e /\ checker_agg_ok tops (expr_type e) /\
     supported_place_expr tops e /\
     (~qualified_place_root e ==> supported_place_info tops e = ValPT (expr_type e))) /\
  (!env e. IS_SOME (type_place_expr env e) ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_expr_refs_ok e) ==>
     supported_place_expr tops e /\
     check_value_type env.type_defs (THE (type_place_expr env e)) /\
     (~qualified_place_root e ==>
      src = NONE /\ supported_place_info tops e = value_type_place (THE (type_place_expr env e)))) /\
  (!env tgt. IS_SOME (type_place_target env tgt) ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_base_target_refs_ok tgt) ==>
     EVERY (supported_pure_expr tops) (target_indices tgt)) /\
  (!env es. well_typed_exprs env es ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_exprs_refs_ok es) ==>
     EVERY (supported_pure_expr tops) es) /\
  (!env opt. well_typed_opt env opt ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_optional_expr_refs_ok opt) ==>
     case opt of NONE => T | SOME e => supported_pure_expr tops e) /\
  (!env kes. well_typed_named_exprs env kes ==>
     linked_body_env tops src tenv env /\ (src = NONE \/ imported_field_refs_ok kes) ==>
     EVERY (supported_pure_expr tops o SND) kes)
Proof
  strip_tac >> ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`supported_pure_expr _ (Name _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           supported_place_info_def, place_type_def, qualified_place_root_def,
           expr_type_def] >> rpt (disch_then strip_assume_tac) >>
      `assignable_type env.type_defs ty` by (fs[linked_body_env_def] >> metis_tac[]) >>
      metis_tac[linked_expr_place_type, checker_agg_ok_def])
  >~ [`supported_pure_expr _ (TopLevelName _ _)`]
  >- MATCH_ACCEPT_TAC linked_toplevel_name_value_supported
  >~ [`supported_pure_expr _ (StructLit _ _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           supported_pure_fields_every, checker_agg_ok_def, expr_type_def,
           place_type_def, supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >>
      gvs[linked_body_env_def] >> metis_tac[linked_structlit_form])
  >~ [`supported_pure_expr _ (Subscript _ _ _)`]
  >- MATCH_ACCEPT_TAC linked_subscript_value_supported
  >~ [`supported_pure_expr _ (Attribute _ _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           supported_place_info_def, place_type_def, expr_type_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >> fs[] >>
      `linked_body_type_facts tops src env.type_defs` by fs[linked_body_env_def] >>
      `supported_field_place tops (expr_type e) id /\ assignable_type env.type_defs ty` by
        metis_tac[linked_attribute_field, imported_expr_refs_type] >>
      simp[] >> metis_tac[checker_agg_ok_def, linked_expr_place_type])
  >~ [`supported_pure_expr _ (Builtin _ _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           supported_pure_exprs_every, expr_type_def, place_type_def,
           supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >> fs[] >>
      `!s b. blt = MakeArray s b ==> supported_place_type tops ty` by
        (rw[] >> fs[] >> metis_tac[linked_expr_place_type]) >>
      drule_all linked_builtin_form >> simp[])
  >~ [`supported_pure_expr _ (TypeBuiltin _ _ _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           supported_pure_exprs_every, expr_type_def, place_type_def,
           supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >> fs[] >>
      `(assignable_type env.type_defs ty ==> supported_place_type tops ty)` by
        metis_tac[linked_expr_place_type] >>
      drule_all linked_type_builtin_form >> simp[])
  >~ [`supported_pure_expr _ (Pop _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, supported_pure_expr_def,
           expr_type_def, place_type_def, supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >>
      fs[assignable_type_def] >> metis_tac[checker_agg_ok_def, linked_expr_place_type])
  >~ [`supported_pure_expr _ (Call _ (IntCall _) _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, imported_call_refs_ok_def,
           supported_pure_expr_def, supported_pure_exprs_every, expr_type_def,
           place_type_def, supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >> fs[] >>
      metis_tac[linked_internal_call, FST])
  >~ [`supported_pure_expr _ (Call _ (ExtCall _ _ _ _) _ _)`]
  >- (simp[well_typed_expr_def, imported_expr_refs_ok_def, imported_call_refs_ok_def,
           supported_pure_expr_def, supported_pure_exprs_every, expr_type_def,
           place_type_def, supported_place_info_def] >>
      rpt (disch_then strip_assume_tac) >> res_tac >> fs[] >>
      Cases_on `ret_ty = NoneT` >> gvs[checker_agg_ok_def] >>
      metis_tac[linked_expr_place_type])
  >~ [`supported_place_expr _ (TopLevelName _ _)`]
  >- MATCH_ACCEPT_TAC linked_toplevel_name_place_supported
  >~ [`supported_place_expr _ (Subscript _ _ _)`]
  >- MATCH_ACCEPT_TAC linked_subscript_place_supported
  >~ [`type_place_target _ (SubscriptTarget _ _)`]
  >- (simp[well_typed_expr_def, target_indices_def, imported_expr_refs_ok_def] >>
      rpt (disch_then strip_assume_tac) >>
      gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> res_tac >> fs[])
  >~ [`type_place_target _ (AttributeTarget _ _)`]
  >- (simp[well_typed_expr_def, target_indices_def, imported_expr_refs_ok_def] >>
      rpt (disch_then strip_assume_tac) >>
      gvs[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >> res_tac >> fs[])
  >> simp[well_typed_expr_def, target_indices_def, imported_expr_refs_ok_def,
          imported_call_refs_ok_def, supported_pure_expr_def, checker_agg_ok_def,
          supported_pure_exprs_every, supported_place_info_def, place_type_def,
          qualified_place_root_def, expr_type_def]
  >> rpt (disch_then strip_assume_tac) >> res_tac >>
  gvs[GSYM checker_agg_ok_def] >>
  TRY (rename1 `well_typed_literal _ lit` >> Cases_on `lit` >>
       fs[well_typed_literal_def] >> NO_TAC) >>
  rw[raw_call_return_type_def, checker_agg_ok_def, supported_place_type_def] >>
  simp[Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def] >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
QED
