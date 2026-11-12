(* Source scope boundaries for a freshly bound loop variable. *)
Theory forPtrSourceScopes
Ancestors
  exprSimSource exprSimHypsDefs vyperTypeInvariants vyperEvalPreservesScopes
  vyperState finite_map list pred_set

Theorem env_scopes_absent_local:
  env_scopes_consistent env cx es /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id es.scopes = NONE
Proof
  rw[env_scopes_consistent_def] >>
  Cases_on `lookup_scopes id es.scopes` >> gvs[FLOOKUP_DEF] >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem fresh_body_scope_shape:
  lookup_scopes id es.scopes = NONE /\
  eval_stmts cx stmts (es with scopes :=
    (FEMPTY |+ (id,entry)) :: es.scopes) = (r,ee) ==>
  ?sc rest. ee.scopes = sc::rest /\
    (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
    lookup_scopes id rest = NONE
Proof
  strip_tac >>
  `ee.scopes <> [] /\ MAP FDOM (TL ee.scopes) = MAP FDOM es.scopes` by
    (drule eval_stmts_preserves_scopes_dom >>
     simp[preserves_scopes_dom_def]) >>
  Cases_on `ee.scopes` >> gvs[] >>
  `lookup_scopes id t = NONE` by
    (irule lookup_scopes_none_map_fdom >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> Cases_on `x = id` >- gvs[] >>
  drule eval_stmts_new_in_head_not_in_tail >> simp[]
QED

Theorem expr_sim_inv_absent_local:
  expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id es.scopes = NONE
Proof
  strip_tac >> irule env_scopes_absent_local >>
  gvs[expr_sim_inv_def, env_consistent_def] >> metis_tac[]
QED
