Theory ctorDeployLoweringEntrySelection
Ancestors
  ctorDeployLoweringDefs ctorDeployInitcode compileVyper e2eDeployDefs

Theorem deploy_ctor_entry_selection_agrees:
  !tops rp runtime unit body ce nr key ut imm lbl sa sb sj se sp sf fn
   bc am tx es mut nr' body' am_c es0.
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) /\
  deploy_state_rel tops bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
  nr' = nr /\ body' = body
Proof
  simp[deploy_ctor_code_def, deploy_state_rel_def, deploy_ctor_start_def] >>
  rpt strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  gvs[package_constructor_def, set_constructor_package_target_def]
QED
