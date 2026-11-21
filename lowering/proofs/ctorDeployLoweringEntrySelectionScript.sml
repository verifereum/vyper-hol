Theory ctorDeployLoweringEntrySelection
Ancestors
  ctorDeployLoweringDefs ctorDeployInitcode compileVyper e2eDeployDefs
  ctorDeployDefs supportedProgram constSubst
  vyperTypeContractStaticMaps list

val _ = Parse.hide "body";

Theorem deploy_ctor_entry_selection_agrees:
  !tops rp runtime unit body ce nr key ut imm lbl sa sb sj se sp sf fn
   bc am tx es mut nr' body' am_c es0.
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) /\
  deploy_state_rel tops bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
  nr' = nr /\ body = subst_consts_stmts (module_consts_env tops []) body'
Proof
  simp[deploy_ctor_code_def, deploy_state_rel_def, deploy_ctor_start_def] >>
  rpt strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    ctorDeployDefsTheory.classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  gvs[subst_consts_fn_def, subst_consts_expr_def, package_constructor_def,
      set_constructor_package_target_def]
QED
