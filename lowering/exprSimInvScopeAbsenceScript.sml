Theory exprSimInvScopeAbsence
Ancestors
  exprBodyPreProps exprSimHypsDefs vyperTypeInvariants vyperState finite_map

Theorem expr_sim_inv_scope_lookup_none:
  expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id es.scopes = NONE
Proof
  strip_tac >>
  `env_consistent env cx es` by
    (fs[expr_sim_inv_split_def] >>
     metis_tac[expr_sim_inv_mods_env]) >>
  Cases_on `lookup_scopes id es.scopes` >> simp[] >>
  fs[env_consistent_def, env_scopes_consistent_def] >>
  qpat_assum `!id entry. lookup_scopes _ _ = SOME _ ==> _`
    (drule_then mp_tac) >> simp[FLOOKUP_DEF]
QED
