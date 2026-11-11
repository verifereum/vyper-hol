(* Reachable source layouts for storage aggregate Append staging. *)
Theory appendAggregateLayout
Ancestors bodyMemAssignTopCopyFacts bodySim exprSimHypsDefs exprSimHyps
  supportedTypes supportedExprs supportedProgram supportedDecls
  exprLowering compileEnv vyperTypeSystem memoryLocalRhsProps

Theorem append_rhs_lowered_layout:
  !cenv e tops ctx cx env es.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    supported_storage_type tops (expr_type e) ==>
    lowered_value_type cenv e = expr_type e \/
    (?et sn dn. lowered_value_type cenv e = ArrayT et (Dynamic sn) /\
      expr_type e = ArrayT et (Dynamic dn) /\
      supported_full_word_type et /\ sn <= dn)
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (simp[vyperASTTheory.expr_type_def] >> metis_tac[topcopy_not_bytestring, is_bytestring_type_def])
  >- (simp[vyperASTTheory.expr_type_def] >> metis_tac[topcopy_not_bytestring, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def, vyperASTTheory.expr_type_def] >>
      strip_tac >> gvs[vyperASTTheory.expr_type_def] >>
      drule topcopy_not_bytestring >>
      gvs[well_typed_builtin_app_def, is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
      simp[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
           vyperASTTheory.expr_type_def] >> strip_tac >>
      gvs[vyperASTTheory.expr_type_def] >>
      drule topcopy_not_bytestring >> simp[is_bytestring_type_def])
  >- (rpt gen_tac >> strip_tac >>
      rename1 `Call ct (IntCall fid) args drv` >>
      `supported_program tops /\
       cenv.ce_func_return_type = build_func_return_type tops /\
       get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      `well_typed_expr env (Call ct (IntCall fid) args drv)` by
        gvs[expr_body_pre_def] >>
      qpat_x_assum `supported_expr _ _` mp_tac >>
      simp[supportedExprsTheory.supported_expr_def, supported_pure_expr_def,
           supported_effect_expr_def] >> strip_tac >>
      Cases_on `drv` >> gvs[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
      PairCases_on `x` >>
      `?sig. FLOOKUP env.fn_sigs fid = SOME sig` by
        (Cases_on `fid` >> gvs[well_typed_expr_def, optionTheory.IS_SOME_EXISTS]) >>
      drule_all supported_internal_signature_return >> strip_tac >>
      drule_all supported_internal_return_admissible >> strip_tac >>
      drule_all supported_internal_return_type >> strip_tac >>
      qpat_x_assum `well_typed_expr _ _` mp_tac >>
      Cases_on `fid` >>
      simp[well_typed_expr_def, vyperASTTheory.expr_type_def] >> strip_tac >>
      gvs[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
      gvs[supported_return_type_def, type_widens_to_def]
      >- (Cases_on `ct` >> gvs[arg_type_fits_def]) >>
      Cases_on `?et dn. ct = ArrayT et (Dynamic dn)`
      >- (pop_assum strip_assume_tac >> gvs[] >>
          Cases_on `sig.ret_ty` >> gvs[arg_type_fits_def] >>
          Cases_on `b` >> gvs[arg_type_fits_def, supported_value_type_def,
            supported_scalar_type_def, supported_word_type_def, supported_string_type_def] >>
          rename1 `supported_word_type sty` >>
          `supported_storage_type tops et` by
            metis_tac[supported_storage_array_depth] >>
          `supported_value_type tops sty` by
            metis_tac[supported_value_type_def, supported_scalar_type_def] >>
          `!et' n. et <> ArrayT et' (Dynamic n)` by
            (Cases_on `sty` >> gvs[supported_word_type_def] >>
             Cases_on `et` >> gvs[arg_type_fits_def]) >>
          `sty = et` by metis_tac[topcopy_value_fit_equal] >>
          gvs[] >> disj2_tac >>
          Cases_on `et` >>
          gvs[supported_word_type_def, supported_storage_type_def,
              Ntimes supported_nested_type_def 2, supported_full_word_type_def]) >>
      disj1_tac >> irule topcopy_value_fit_equal >> metis_tac[]) >>
  simp[lowered_value_type_def]
QED
