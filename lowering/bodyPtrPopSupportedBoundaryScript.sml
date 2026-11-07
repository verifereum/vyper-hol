Theory bodyPtrPopSupportedBoundary
Ancestors bodyPtrPopEffectClassification bodyPtrPopRootLocationBoundary
  exprLowering compileEnv context finite_map

Theorem pop_toplevel_target_literal:
  compile_get_target_ptr cfn cenv (TopLevelNameTarget id) sa = ((op,lo,pt),sb) ==>
  sb = sa /\ ?h. op = Lit h
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP cenv.ce_module_vars id` >> simp[comp_return_def] >>
  Cases_on `x` >> simp[comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem pop_literal_scaled_locations_boundary:
  pop_comp_boundary sa /\
  compile_dynarray_pop (Lit h) (word_scale loc) esz ctor imm loc sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `loc` >> simp[word_scale_def] >> rpt strip_tac
  >- (drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
        pop_nonstorage_dynarray_boundary >> simp[])
  >- (drule_all pop_literal_all_locations_boundary >> simp[])
  >- (drule_all pop_literal_all_locations_boundary >> simp[])
  >> drule_at (Pat `compile_dynarray_pop _ _ _ _ _ _ _ = _`)
       pop_nonstorage_dynarray_boundary >> simp[]
QED

Theorem pop_toplevel_expr_boundary:
  pop_comp_boundary sa /\
  compile_expr cenv ty (Pop v10 (TopLevelNameTarget id)) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[Once compile_expr_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  drule pop_toplevel_target_literal >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule_all pop_literal_scaled_locations_boundary >> simp[]
QED

Theorem pop_supported_expr_boundary:
  supportedExprs$supported_expr tops (Pop v10 bt) /\ pop_comp_boundary sa /\
  compile_expr cenv ty (Pop v10 bt) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[pop_supported_target_shape] >> rpt strip_tac >> gvs[] >>
  drule_all pop_toplevel_expr_boundary >> simp[]
QED
