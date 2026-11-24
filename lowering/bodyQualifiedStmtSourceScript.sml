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
  Induct_on `tops` >- simp[] >>
  rpt strip_tac >>
  `event_decl_unique name tops` by
    (fs[event_decl_unique_def] >> metis_tac[]) >>
  Cases_on `h` >> fs[supported_event_fields_def] >>
  rename1 `EventDecl event_name declared_fields` >>
  Cases_on `event_name = name` >> fs[] >>
  fs[event_decl_unique_def] >> metis_tac[]
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
  simp[qualified_stmt_decls_ok_def, custom_errors_stmt_ok_def]
  >- (Cases_on `err` >> simp[])
  >- (Cases_on `err` >> simp[])
  >- (PairCases_on `id` >> Cases_on `id0` >> simp[type_log_inversion] >>
      strip_tac >> gvs[] >>
      drule_all_then strip_assume_tac checked_event_fields >>
      map_every qexists_tac [`tops`, `fields`] >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (If _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
      strip_tac >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (For _ _ _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
      strip_tac >> metis_tac[])
  >> rpt strip_tac >> Cases_on `type_stmt env ret s` >>
  gvs[type_stmt_def] >>
  drule type_stmt_preserves_event_fields >> metis_tac[]
QED

Theorem checked_body_qualified_stmt_decls:
  check_contract dep layouts addr mods = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmts env ret ss = SOME env' /\ custom_errors_stmts_ok mods ss ==>
  qualified_stmts_decls_ok mods ss
Proof
  strip_tac >>
  drule_then assume_tac check_contract_namespaces_ok >>
  `art.cta_event_fields = (build_contract_type_artifact dep mods).cta_event_fields` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def, COND_RAND, COND_RATOR] >>
     strip_tac >> gvs[live_artifact_event_fields]) >>
  metis_tac[cj 2 qualified_stmt_decls_from_typing]
QED
