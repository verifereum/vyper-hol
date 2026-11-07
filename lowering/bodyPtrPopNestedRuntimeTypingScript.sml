Theory bodyPtrPopNestedRuntimeTyping
Ancestors exprSimPopNested targetPlaceSimCases vyperTypeEnv exprSimHypsDefs
  exprSimDefs vyperAST targetPlaceSim vyperTypeInvariants vyperTypeSystem

(* Runtime target-to-declaration boundary remains to be proved. *)

Theorem pop_runtime_target_declaration:
  !bt env cx src id.
  env_context_consistent env cx /\ ~cx.in_deploy /\
  type_place_target env bt <> NONE /\
  target_root bt = TopLevelNameTarget (src,id) ==>
  ?ts d. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_root_def] >> rpt strip_tac
  >- (Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> gvs[] >>
      gvs[type_place_target_TopLevelNameTarget,
          env_context_consistent_def, bare_global_assignable_complete_def] >>
      Cases_on `x` >> gvs[] >> metis_tac[optionTheory.option_CASES]) >>
  qpat_x_assum `type_place_target env _ <> NONE` mp_tac >>
  qmatch_goalsub_abbrev_tac `type_place_target env tgt` >>
  Cases_on `type_place_target env tgt` >> simp[] >>
  gvs[Abbr `tgt`, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget] >>
  first_x_assum irule >> simp[expr_size_def] >> qexistsl_tac [`env`,`b`] >>
  simp[expr_size_def]
QED

Theorem pop_pre_runtime_target_declaration:
  ~cx.in_deploy /\ expr_body_pre cenv cx env (Pop ann bt) es /\
  target_root bt = TopLevelNameTarget (src,id) ==>
  ?ts d. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d
Proof
  rpt strip_tac >> irule pop_runtime_target_declaration >>
  simp[] >> qexistsl_tac [`bt`,`env`] >> simp[] >> reverse conj_tac
  >- metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED
