Theory bodyNestedMapChildMods
Ancestors
  bodyFullPredsMods

(* The enclosing value Subscript uses the map clause of its nested base IH. *)
Theorem nested_subscript_map_child_mods:
  !mods exps cx ann a b i idx kt vt
   DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
    body_expr_full_ok_mods mods exps cx (Subscript a b i) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Subscript ann (Subscript a b i) idx) es /\
    place_type cenv (Subscript a b i) = MapPT kt vt ==>
    expr_map_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Subscript a b i) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac expr_body_pre_mods_map_subscript_base >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!ann e1 e2 DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                 _ ==> expr_map_sim_full_mods _ _ _ _ _ _` irule >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`src`, `tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED
