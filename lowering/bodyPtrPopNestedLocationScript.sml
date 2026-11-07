Theory bodyPtrPopNestedLocation
Ancestors bodyPtrPopNestedHeader bodyPtrPopNestedRuntimeTyping targetPlaceSim
  exprLowering compileEnv vyperAST

Libs dep_rewrite

Theorem pop_target_root_location:
  !bt f g cenv sa hdr lo pt sb sc rh rl rpt sd.
  compile_get_target_ptr f cenv bt sa = ((hdr,lo,pt),sb) /\
  compile_get_target_ptr g cenv (target_root bt) sc = ((rh,rl,rpt),sd)
  ==> lo = rl
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_root_def] >> rpt strip_tac
  >~ [`compile_get_target_ptr _ _ (NameTarget _) _ = _`]
  >- (Cases_on `FLOOKUP cenv.ce_vars s` >>
      gvs[compile_get_target_ptr_def, comp_return_def] >>
      Cases_on `x` >> gvs[comp_return_def])
  >~ [`compile_get_target_ptr _ _ (TopLevelNameTarget _) _ = _`]
  >- (Cases_on `FLOOKUP cenv.ce_module_vars p` >>
      gvs[compile_get_target_ptr_def, comp_return_def] >>
      Cases_on `x` >> gvs[comp_return_def]) >>
  Cases_on `compile_get_target_ptr f cenv b sa` >>
  PairCases_on `q` >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  `q1 = rl` by (first_x_assum irule >> metis_tac[]) >>
  qpat_x_assum `compile_get_target_ptr f cenv _ sa = ((hdr,lo,pt),sb)` mp_tac >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  Cases_on `q2` >> simp[comp_bind_def, comp_return_def] >>
  TRY (Cases_on `x` >> simp[comp_bind_def, comp_return_def]) >>
  rpt (pairarg_tac >> gvs[]) >> simp[comp_return_def]
QED

Theorem pop_nested_root_nonstorage:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn cenv cx es s /\
  (~(?id. bt = NameTarget id)) /\
  (~(?nid. bt = TopLevelNameTarget nid)) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,lo,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sa sb fn /\
  compile_get_target_ptr g cenv (target_root bt) sc = ((rh,rl,rpt),sd)
  ==> rl <> SOME LocStorage /\ rl <> SOME LocTransient
Proof
  rpt strip_tac >>
  drule_all pop_nested_entry_nonstorage >>
  drule_all pop_target_root_location >> simp[]
QED
