(* Assemble the linked Not value and VV routes at the typed unary operand. *)
Theory bodyWordNotRouteMods
Ancestors
  bodyWordNotShapeMods bodyWordNotEndpointMods bodyScalarStackVVMods
  bodyFullPredsMods exprBodyPreProps exprSimUnopProps exprLoweringProps
  vyperTypeSystem vyperContext vyperAST loweringPosts

Theorem word_not_sim_mods:
  !mods exps DF lo d ctx shadow_ctx PG src tops func shadow_func cenv env cx ty a bt args es.
    bt = Not /\
    (builtin_args_length_ok bt (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `builtin_args_length_ok Not (LENGTH args)` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def, builtin_args_length_ok_def]) >>
  `body_exprs_full_ok_mods mods exps cx args` by simp[] >>
  drule_all_then (qx_choose_then `e` (map_every assume_tac o CONJUNCTS)) word_not_shape_mods >>
  gvs[] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
        _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _` mp_tac >>
     metis_tac[]) >>
  conj_asm1_tac
  >- (irule word_not_value_sim_mods >> simp[] >>
      qexistsl_tac [`env`, `exps`, `mods`, `src`, `tops`] >> simp[]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[compile_not_abs_stack, post_value_type_def, expr_type_def] >>
  rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value
QED
