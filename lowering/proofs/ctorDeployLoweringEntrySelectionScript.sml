Theory ctorDeployLoweringEntrySelection
Ancestors
  ctorDeployLoweringDefs ctorDeployInitcode compileVyper e2eDeployDefs
  ctorDeployDefs supportedProgram constSubst constSubstStmtsPreserve
  vyperTypeContractStaticMaps list

val _ = Parse.hide "body";

Theorem deploy_supported_constructor_subst:
  deploy_source_ok tops am tx /\
  vyperInterpreter$lookup_function NONE name Deploy tops =
    SOME (mut,nr,args,[],NoneT,body) ==>
  subst_consts_stmts (module_consts_env tops []) body = body
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac
  >- gvs[subst_consts_stmt_def] >>
  `supported_program_deploy tops /\ deploy_typing_ok tops am tx` by
    fs[deploy_source_ok_def] >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_typing_ok_def] >>
  `ALOOKUP [((NONE:num option),tops)] NONE = SOME tops` by simp[] >>
  drule_all checked_constructor_body_subst >> simp[]
QED

Theorem deploy_ctor_entry_selection_agrees:
  !tops rp runtime unit body ce nr key ut imm lbl sa sb sj se sp sf fn
   bc am tx es mut nr' body' am_c es0.
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,fn) /\
  deploy_state_rel tops bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) ==>
  nr' = nr /\ body' = body
Proof
  simp[deploy_ctor_code_def, deploy_state_rel_def, deploy_ctor_start_def] >>
  rpt strip_tac >>
  drule_all deploy_supported_constructor_subst >> strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >> strip_tac >>
  PairCases_on `cf` >> gvs[ctor_named_init_def] >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    ctorDeployDefsTheory.classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  gvs[subst_consts_fn_def, subst_consts_expr_def, package_constructor_def,
      set_constructor_package_target_def]
QED
