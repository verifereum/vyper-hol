Theory deployOutcomesFreeConstructorTyping
Ancestors
  ctorDeployDefs ctorDeployShape ctorDeployInitcode
  vyperTypeContractContext vyperTypeContract compileVyper
  e2eDeployDefs vyperTypeSystem supportedStmtTraverse

Theorem outcomes_free_classified_constructor_typing:
  !layouts addr mods art tops mut nr rr fname args defaults ret fbody.
  check_contract T layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,fname,args,defaults,ret,fbody) ==>
  ?env env'. type_stmts env ret fbody = SOME env'
Proof
  rpt gen_tac >> strip_tac >>
  drule classify_functions_ctor_mem >> strip_tac >>
  drule_all check_contract_deploy_function_body_MEM >>
  simp[check_function_body_def] >>
  strip_tac >>
  Cases_on `type_stmts (function_entry_env art mods NONE Deploy args) ret fbody` >>
  gvs[] >> metis_tac[]
QED

Theorem outcomes_free_classified_constructor_source:
  !tops am tx mut nr rr fname args dflts ret fbody.
  deploy_source_ok tops am tx /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,fname,args,dflts,ret,fbody) /\
  ctor_named_init (SOME (mut,nr,rr,fname,args,dflts,ret,fbody)) ==>
  ?env env'. type_stmts env ret fbody = SOME env' /\
    ~supported_stmts_expr_exists constructor_call_root fbody
Proof
  rpt gen_tac >> strip_tac >>
  fs[deploy_source_ok_def, deploy_typing_ok_def, ctor_named_init_def] >>
  `ALOOKUP [(NONE,tops)] NONE = SOME tops` by simp[] >>
  `?env env'. type_stmts env ret fbody = SOME env'` by
    (irule (INST_TYPE [``:'a`` |-> ``:160 word``]
       outcomes_free_classified_constructor_typing) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qspec_then `tops` (qspecl_then [`NONE`, `"__init__"`] mp_tac)
    classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  fs[constructor_call_free_def] >> metis_tac[]
QED

(* This is the very package consumed by lower_vyper_deploy_unit, including
   its empty-body default when classification found no constructor. *)
Theorem outcomes_free_constructor_package_source:
  !tops am tx ctor target use_trans nkeys cenv args pay nr key ut fbody ret.
  deploy_source_ok tops am tx /\
  SND (SND (SND (classify_functions tops))) = ctor /\
  ctor_named_init ctor /\
  set_constructor_package_target target
    (case ctor of
       SOME cf => package_constructor tops use_trans nkeys cf
     | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                F, F, 0n, F, ([] : stmt list), NoneT)) =
    (cenv,args,pay,nr,key,ut,fbody,ret) ==>
  ?env env'. type_stmts env ret fbody = SOME env' /\
    ~supported_stmts_expr_exists constructor_call_root fbody
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ctor`
  >- (gvs[set_constructor_package_target_def] >>
      simp[type_stmt_def, supported_stmt_expr_exists_def]) >>
  rename1 `SOME cf` >> PairCases_on `cf` >>
  `?env env'. type_stmts env cf6 cf7 = SOME env' /\
    ~supported_stmts_expr_exists constructor_call_root cf7` by
    (irule outcomes_free_classified_constructor_source >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  gvs[set_constructor_package_target_def, package_constructor_def] >>
  metis_tac[]
QED
