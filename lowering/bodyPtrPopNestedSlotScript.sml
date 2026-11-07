Theory bodyPtrPopNestedSlot
Ancestors bodyPtrPopNestedBinding bodyPtrPopNestedRuntimeTyping
  targetPlaceSim vyperTypeEnv vyperTypeInvariants vyperTypeSystem
  exprSimHypsDefs exprSimDefs vyperAST vyperState compileEnv

(* The contrapositive helper in exprSimPopNested is local. *)
Theorem pop_target_root_typed:
  !bt env. type_place_target env bt <> NONE ==>
    type_place_target env (target_root bt) <> NONE
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_root_def] >> rpt strip_tac >>
  qpat_x_assum `type_place_target env _ <> NONE` mp_tac >>
  qmatch_goalsub_abbrev_tac `type_place_target env tgt` >>
  Cases_on `type_place_target env tgt` >> simp[] >>
  gvs[Abbr `tgt`, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget] >>
  first_x_assum irule >> simp[expr_size_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem pop_runtime_target_slot:
  env_consistent env cx es /\ ~cx.in_deploy /\
  type_place_target env bt <> NONE /\
  target_root bt = TopLevelNameTarget (src,name) ==>
  ?ts d id slot. get_module_code cx src = SOME ts /\
    find_var_decl_by_name name ts = SOME (d,id) /\
    lookup_var_slot_from_layout cx (var_decl_transient d) src id = SOME slot
Proof
  strip_tac >> drule pop_target_root_typed >>
  asm_rewrite_tac[] >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,name))` >> simp[] >>
  `env.bare_global_assignable = FEMPTY` by
    metis_tac[env_consistent_def, env_context_consistent_def,
              bare_global_assignable_complete_def] >>
  gvs[type_place_target_TopLevelNameTarget] >>
  Cases_on `x`
  >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      gvs[optionTheory.IS_SOME_EXISTS] >>
      simp[var_decl_transient_def] >>
      metis_tac[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  simp[var_decl_transient_def] >> metis_tac[]
QED

Theorem pop_pre_runtime_target_slot:
  ~cx.in_deploy /\ expr_body_pre cenv cx env (Pop ann bt) es /\
  target_root bt = TopLevelNameTarget (src,name) ==>
  ?ts d id slot. get_module_code cx src = SOME ts /\
    find_var_decl_by_name name ts = SOME (d,id) /\
    lookup_var_slot_from_layout cx (var_decl_transient d) src id = SOME slot
Proof
  strip_tac >> irule pop_runtime_target_slot >>
  simp[] >> qexistsl_tac [`bt`,`env`,`es`] >> simp[] >> reverse conj_tac
  >- metis_tac[expr_body_pre_def, expr_sim_inv_def] >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem pop_nested_module_root_exclusion:
  body_inv tops ctx cenv cx /\ ~cx.in_deploy /\
  stmt_state_rel ctx fn cenv cx es s /\
  (~(?id. bt = NameTarget id)) /\
  (~(?nid. bt = TopLevelNameTarget nid)) /\
  compile_get_target_ptr compile_expr cenv bt sa = ((hdr,lo,pt),sm) /\
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  fn_has_code sa sb fn /\
  target_root bt = TopLevelNameTarget (src,name) /\
  expr_body_pre cenv cx env (Pop ann bt) es ==> F
Proof
  strip_tac >> drule_all pop_pre_runtime_target_slot >> strip_tac >>
  drule_all pop_nested_declared_slot_exclusion >> simp[]
QED
