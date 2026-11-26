(* Request-prefix companion to bodyFullSubscriptMap. *)
Theory s1PrefixSubscriptMap
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixSubscriptMapParts
  s1PrefixSubscriptMapSelect s1PrefixSubscriptMapCompose
  exprSimSubscriptMap exprSimMapDefs exprSimDefs exprSimHypsDefs
  placeTypingProps exprLowering vyperTypeSystem exprSimInvPlaceMapProjection

fun mapping_children_prefix_tac admissible =
  drule_all mapping_subscript_prefix_parts >> strip_tac >>
  irule mapping_subscript_children_prefix >>
  rpt conj_tac >> FIRST [
    first_assum ACCEPT_TAC,
    rpt gen_tac >> MATCH_ACCEPT_TAC mapping_select_no_request_outcome,
    qexists_tac admissible >>
      simp[expr_vv_res_ok_def,expr_map_res_ok_def,expr_res_ok_def],
    goal_assum (drule_at (Pat `compile_expr _ _ (gas_shadow_expr _) _ = _`)) >>
    goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
    goal_assum (drule_at (Pat `lower_value _ _ _ (gas_shadow_expr _) _ = _`)) >>
    goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
    goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
    goal_assum (drule_at (Pat `place_type _ _ = MapPT _ _`)) >>
    goal_assum (drule_at (Pat `body_const_cells_agree _ _ _ _`)) >>
    goal_assum (drule_at (Pat `gas_shadow_function _ _`)) >> simp[]];

Theorem subscript_map_map_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_map_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es /\
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es ==>
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_map_pre_subscript_base >> strip_tac >>
  `?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt)` by fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined cenv env` by
    (`expr_sim_inv cenv cx env es` by
       (qpat_assum `expr_map_pre _ _ _ e1 _`
          (mp_tac o REWRITE_RULE [expr_map_pre_def]) >> simp[]) >>
     drule_then ACCEPT_TAC expr_sim_inv_place_map_tables_agree_on_defined) >>
  drule_all place_type_checked_place_on_defined >> simp[value_type_place_def] >>
  strip_tac >> drule map_base_no_overlap >>
  disch_then (qspecl_then [`cenv`,`e2`,`cx`] strip_assume_tac) >>
  rewrite_tac[expr_map_sim_prefix_def,expr_map_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >> mapping_children_prefix_tac `expr_map_res_ok`
QED

Theorem subscript_map_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es kt vt.
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  place_type cenv e1 = MapPT kt vt /\
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e1 es /\
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e1 es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_map_subscript_base >> strip_tac >>
  drule_all expr_map_pre_checked_type >> strip_tac >>
  drule map_base_no_overlap >>
  disch_then (qspecl_then [`cenv`,`e2`,`cx`] strip_assume_tac) >>
  rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >> mapping_children_prefix_tac `expr_vv_res_ok`
QED
