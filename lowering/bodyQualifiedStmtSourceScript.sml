(* The checked event table and custom-error traversal discharge the
   qualified declaration checks used by the body simulation. *)
Theory bodyQualifiedStmtSource
Ancestors
  bodyQualifiedStmtSupport supportedDecls vyperTypeEventLookup
  vyperTypeContractContext vyperTypeEnvExtension vyperTypeContract vyperEvent
  vyperEventArgCompat vyperTypeSystem vyperAST finite_map alist list

Triviality event_fields_from_unique_decl:
  !tops. event_decl_unique name tops /\ MEM (EventDecl name fields) tops ==>
    supported_event_fields tops (NONE,name) = SOME fields
Proof
  Induct >> simp[supported_event_fields_def, event_decl_unique_def] >>
  Cases >> simp[supported_event_fields_def, event_decl_unique_def] >>
  Cases_on `s = name` >> simp[] >> metis_tac[]
QED

Triviality checked_event_fields:
  contract_namespaces_ok dep mods /\
  FLOOKUP (build_contract_type_artifact dep mods).cta_event_fields (src,name) = SOME fields ==>
  ?tops. ALOOKUP mods src = SOME tops /\
    supported_event_fields tops (NONE,name) = SOME fields
Proof
  strip_tac >>
  drule_then (qx_choose_then `tops` strip_assume_tac) build_contract_event_fields_sound >>
  qexists_tac `tops` >> conj_tac
  >- (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  irule event_fields_from_unique_decl >>
  metis_tac[contract_namespaces_ok_event_decl_unique]
QED

Triviality qualified_stmt_decls_from_typing:
  (!env ret s env'.
     type_stmt env ret s = SOME env' /\
     env.event_fields = (build_contract_type_artifact dep mods).cta_event_fields /\
     custom_errors_stmt_ok mods s /\ contract_namespaces_ok dep mods ==>
     qualified_stmt_decls_ok mods s) /\
  (!env ret ss env'.
     type_stmts env ret ss = SOME env' /\
     env.event_fields = (build_contract_type_artifact dep mods).cta_event_fields /\
     custom_errors_stmts_ok mods ss /\ contract_namespaces_ok dep mods ==>
     qualified_stmts_decls_ok mods ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[qualified_stmt_decls_ok_def, custom_errors_stmt_ok_def,
       type_log_inversion, local_env_event_fields] >>
  rpt strip_tac >>
  gvs[type_stmt_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS,
      custom_errors_stmt_ok_def, local_env_event_fields] >>
  imp_res_tac type_stmt_preserves_event_fields >> gvs[] >>
  res_tac >> gvs[]
  >- (Cases_on `err` >> gvs[custom_errors_stmt_ok_def])
  >- (Cases_on `err` >> gvs[custom_errors_stmt_ok_def])
  >> PairCases_on `id` >> Cases_on `id0` >> simp[] >>
  drule_all_then strip_assume_tac checked_event_fields >> metis_tac[]
QED

Theorem checked_body_qualified_stmt_decls:
  check_contract dep layouts addr mods = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmts env ret ss = SOME env' /\ custom_errors_stmts_ok mods ss ==>
  qualified_stmts_decls_ok mods ss
Proof
  strip_tac >>
  `art.cta_event_fields = (build_contract_type_artifact dep mods).cta_event_fields` by
    gvs[check_contract_def, AllCaseEqs()] >>
  drule_then assume_tac check_contract_namespaces_ok >>
  metis_tac[cj 2 qualified_stmt_decls_from_typing]
QED
