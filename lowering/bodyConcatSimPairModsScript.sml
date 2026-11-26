(* Close the public Concat fold at the linked expression boundary. *)
Theory bodyConcatSimPairMods
Ancestors
  bodyConcatRouteMods bodyConcatElementsMods bodyFullPredsMods
  vyperAST vyperTypeSystem

Theorem concat_sim_pair_mods:
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es
Proof
  strip_tac >> ONCE_REWRITE_TAC [CONJ_COMM] >>
  irule concat_from_elements_mods >>
  pure_rewrite_tac [EQT_INTRO concat_elements_mods, AND_CLAUSES] >>
  map_every qexists_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
