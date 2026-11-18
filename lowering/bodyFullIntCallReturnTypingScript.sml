Theory bodyFullIntCallReturnTyping
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams exprSimHyps vyperTyping vyperTypeArgFits

Theorem intcall_declared_return_type:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ret /\
  type_widens_to (get_tenv cx) ret ann
Proof
 strip_tac >>
 `get_module_code cx NONE = SOME tops` by
   fs[bodySimTheory.body_inv_def] >>
 `expr_sim_inv cenv cx tenv es0 /\
   well_typed_expr tenv (Call ann (IntCall (NONE,name)) es dflt)` by
   fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
 `?sig. FLOOKUP tenv.fn_sigs (NONE,name) = SOME sig` by
   fs[vyperTypeSystemTheory.well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >>
 `cenv.ce_func_return_type (nsid_to_string (NONE,name)) = sig.ret_ty /\
   fn_sigs_consistent tenv.fn_sigs cx /\ tenv.type_defs = get_tenv cx` by
   (qhdtm_assum `expr_sim_inv` mp_tac >>
    pure_rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_def,
                     vyperTypeInvariantsTheory.env_consistent_def,
                     vyperTypeInvariantsTheory.env_context_consistent_def] >>
    strip_tac >>
    metis_tac[]) >>
 `sig.ret_ty = ret` by
   (qhdtm_x_assum `fn_sigs_consistent` mp_tac >>
    pure_rewrite_tac[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
    disch_then drule >> simp[]) >>
 `type_widens_to (get_tenv cx) ret ann` by
   fs[vyperTypeSystemTheory.well_typed_expr_def] >> simp[]
QED

Theorem intcall_rest_read_post_typed:
 !tops ctx cenv cx tenv ann name es dflt es0 mut nr args ret ss rtv
  prev start tv ee rt v dflts.
 body_inv tops ctx cenv cx /\
 expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
 lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
 evaluate_type (get_tenv cx) ret = SOME rtv /\
 intcall_rest cx name mut nr ss prev rtv start = (INL tv,ee) /\
 evaluate_type (get_tenv cx)
   (post_value_type cenv (Call ann (IntCall (NONE,name)) es dflt)) = SOME rt /\
 read_result cx tv ee = (INL v,ee) ==>
 value_has_type rt v
Proof
 rpt gen_tac >> strip_tac >>
 `value_has_type rtv v` by
   (qpat_x_assum `intcall_rest _ _ _ _ _ _ _ _ = _` mp_tac >>
    pure_rewrite_tac[intcall_rest_def, vyperStateTheory.ignore_bind_def] >>
    simp_tac pure_ss [vyperStateTheory.bind_def, AllCaseEqs(),
      vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def,
      pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
    strip_tac >> gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
    Cases_on `safe_cast rtv rv` >>
    gvs[vyperStateTheory.raise_def, vyperStateTheory.return_def] >>
    metis_tac[safe_cast_result_well_typed]) >>
 drule_all intcall_declared_return_type >> strip_tac >>
 Cases_on `is_word_type ann \/ is_bytestring_type ann`
 >- (gvs[loweringPostsTheory.post_value_type_def] >>
     drule_all type_widens_to_value_has_type >> simp[]) >>
 gvs[loweringPostsTheory.post_value_type_def, exprLoweringTheory.lowered_value_type_def]
QED
