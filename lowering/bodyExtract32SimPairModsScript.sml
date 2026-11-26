(* Adapt the reached TypeBuiltin arity callback to the linked Extract32 route. *)
Theory bodyExtract32SimPairMods
Ancestors
  bodyAggregateArityMods bodyExtractOperandsMods bodyFullPredsMods
  vyperInterpreter vyperAST

Theorem extract32_sim_pair_mods:
  !mods exps cx ann dst args DF lo d ctx shadow_ctx PG func shadow_func
    cenv env src tops ty es.
    (!s x t. type_check (type_builtin_args_length_ok Extract32 (LENGTH args))
      "TypeBuiltin args" s = (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Extract32 dst args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TypeBuiltin ann Extract32 dst args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TypeBuiltin ann Extract32 dst args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac type_builtin_args_at_arity_mods >>
  irule extract32_from_cuts_mods >>
  map_every qexists_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
