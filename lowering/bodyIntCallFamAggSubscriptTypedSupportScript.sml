(* Typed value support at Subscript children; mapping places stay separate. *)
Theory bodyIntCallFamAggSubscriptTypedSupport
Ancestors
  bodyIntCallFamAggAttributeTypedSupport exprSimSubscriptArraySource
  bodySim exprSimHypsDefs supportedExprs supportedExprForms exprLowering

Theorem supported_subscript_index:
  supported_expr tops (Subscript ann obj idx) ==> supported_expr tops idx
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[]
QED

Theorem supported_subscript_value_base:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Subscript ann obj idx) es /\
  supported_expr tops (Subscript ann obj idx) /\
  supported_place_type tops (expr_type obj) ==> supported_expr tops obj
Proof
  strip_tac >>
  `expr_type obj <> NoneT` by
    (strip_tac >>
     fs[supportedTypesTheory.supported_place_type_def,
        Once supportedTypesTheory.supported_nested_type_def,
        supportedTypesTheory.supported_scalar_type_def,
        supportedTypesTheory.supported_word_type_def,
        supportedTypesTheory.supported_string_type_def]) >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env obj` by
    (conj_tac >- fs[expr_body_pre_def] >>
     `well_typed_expr env (Subscript ann obj idx)` by fs[expr_body_pre_def] >>
     qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
     simp[Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >> strip_tac >>
     irule type_place_expr_context_value_typed >>
     conj_tac >- (qexists_tac `expr_type obj` >> simp[]) >>
     qexists_tac `cx` >>
     fs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def]) >>
  fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  metis_tac[supported_typed_place_expr, supported_typed_effect_place_expr]
QED

Theorem supported_array_subscript_base_type:
  body_inv tops ctx ce cx /\
  supported_expr tops (Subscript ann obj idx) /\
  place_type ce obj = ValPT (ArrayT et bd) /\ expr_type obj = ArrayT et bd ==>
  supported_place_type tops (expr_type obj)
Proof
  strip_tac >>
  `supported_place_info tops obj = place_type ce obj` by
    (pure_rewrite_tac[supported_place_info_def] >> irule place_type_env_cong >>
     fs[body_inv_def]) >>
  fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
     supported_subscript_place_def]
QED
