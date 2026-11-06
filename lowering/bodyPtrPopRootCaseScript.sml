Theory bodyPtrPopRootCase
Ancestors
  bodyPtrPopRootOutcome bodyPtrPopRootEntry bodyPtrPreds bodyPtrDefs
  exprPtrUnwrap exprLoweringProps compileEnv

Theorem pop_root_vv_ptr:
  expr_body_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  strip_tac >> drule pop_root_body_pre >> strip_tac >>
  rw[expr_vv_sim_ptr_def] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all pop_root_storage_entry >> strip_tac >>
  drule_all compile_pop_storage_normalized_ptr >>
  simp[expr_vv_sim_ptr_def] >>
  disch_then irule >> simp[] >> qexists_tac `ty` >> simp[]
QED

Theorem body_pop_root_ptr_ok:
  !cx ann nid. body_expr_ptr_ok cx (Pop ann (TopLevelNameTarget nid))
Proof
  rpt gen_tac >> PairCases_on `nid` >> rw[body_expr_ptr_ok_def] >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann (TopLevelNameTarget (nid0,nid1))) es` by
    (irule pop_root_vv_ptr >> goal_assum (drule_at Any)) >>
  simp[] >> irule expr_sim_ptr_of_vv >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `env` >> simp[]
QED
