Theory bodyAttributeCaseMods
Ancestors
  bodyFullPredsMods bodyAttributePreMods bodyFullAttributeMods

Theorem body_attribute_case_full_mods:
  !mods exps cx v9 e id.
    body_expr_full_ok_mods mods exps cx e ==>
    body_expr_full_ok_mods mods exps cx (Attribute v9 e id)
Proof
  rpt gen_tac >> disch_tac >>
  simp[Once body_expr_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_then assume_tac attribute_pre_child_mods >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e` mp_tac >>
  simp[Once body_expr_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                 _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _`
    (drule_all_then assume_tac) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es`
    by first_assum MATCH_ACCEPT_TAC >>
  drule_all_then ACCEPT_TAC attribute_sim_full_mods_of_child
QED
