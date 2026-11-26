(* A Log uses the source selected by its qualified event key, not the
   module in which the enclosing function happens to be running. *)
Theory bodyLogEventLookupMods
Ancestors
  bodyFullPredsMods bodyQualifiedStmtSupport bodyInvSplit bodyInvMetadataProps
  vyperTypeContract vyperTypeContractContext vyperTypeEventLookup vyperEvent
  bodyCallSupport supportedDecls supportedTypes compileUnit linkedNsidProps
  list pair alist
Libs dep_rewrite

Theorem log_supported_event_member[local]:
  !ts. supported_event_fields ts (NONE,name) = SOME fs ==>
       MEM (EventDecl name fs) ts
Proof
  Induct >> simp[supported_event_fields_def] >>
  Cases >> simp[supported_event_fields_def] >> rw[] >> gvs[]
QED

Theorem log_event_src_fold[local]:
  !ts init.
    (!name fs. MEM (EventDecl name fs) ts /\ nsid_to_string (src,name) = key ==>
       (event_hash tenv name (MAP (SND o FST) fs), MAP (SND o FST) fs, MAP SND fs) = info) ==>
    build_event_info_src tenv src ts init key =
      if ?name fs. MEM (EventDecl name fs) ts /\ nsid_to_string (src,name) = key
      then SOME info else init key
Proof
  Induct >> simp[build_event_info_src_def] >>
  Cases >> simp[build_event_info_src_def] >>
  rpt strip_tac >>
  simp[GSYM LEFT_EXISTS_AND_THM, RIGHT_AND_OVER_OR, EXISTS_OR_THM, EQ_SYM_EQ] >>
  metis_tac[]
QED

Theorem log_event_mods_fold[local]:
  !mods init.
    (!src ts name fs. MEM (src,ts) mods /\ MEM (EventDecl name fs) ts /\
       nsid_to_string (src,name) = key ==>
       (event_hash tenv name (MAP (SND o FST) fs), MAP (SND o FST) fs, MAP SND fs) = info) ==>
    build_event_info_mods tenv mods init key =
      if ?src ts name fs. MEM (src,ts) mods /\ MEM (EventDecl name fs) ts /\
                         nsid_to_string (src,name) = key
      then SOME info else init key
Proof
  Induct >> simp[build_event_info_mods_def] >>
  gen_tac >> PairCases_on `h` >> simp[build_event_info_mods_def] >>
  rpt gen_tac >> disch_tac >>
  `!src ts name fs. MEM (src,ts) mods /\ MEM (EventDecl name fs) ts /\
     nsid_to_string (src,name) = key ==>
     (event_hash tenv name (MAP (SND o FST) fs), MAP (SND o FST) fs, MAP SND fs) = info`
    by metis_tac[] >>
  qpat_assum `!init. _ ==> build_event_info_mods _ _ init _ = _`
    (qspec_then `build_event_info_src tenv h0 h1 init` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  qspecl_then [`h1`,`init`] mp_tac (Q.INST [`info` |-> `info`, `src` |-> `h0`]
    log_event_src_fold) >>
  impl_tac >- (rpt strip_tac >>
    qpat_assum `!src ts name fs. (_ \/ MEM _ mods) /\ _ ==> _`
      (qspecl_then [`h0`,`h1`,`name`,`fs`] mp_tac) >> simp[]) >>
  disch_then (fn th => simp[th]) >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  Cases_on `?src ts name fs. MEM (src,ts) mods /\ MEM (EventDecl name fs) ts /\
                             nsid_to_string (src,name) = key` >> simp[]
QED

Theorem log_event_lookup_mods:
  contract_inv mods exps ctx ce cx /\
  body_const_cells_agree_mods mods cx env es /\
  qualified_stmt_decls_ok mods (Log id args) ==>
  ?ts fields h.
    ALOOKUP mods (FST id) = SOME ts /\
    supported_event_fields ts (NONE,SND id) = SOME fields /\
    LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields /\
    ce.ce_event_info (nsid_to_string id) = SOME (h,MAP (SND o FST) fields,MAP SND fields) /\
    lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id =
      SOME (h,MAP (SND o FST) fields,MAP SND fields) /\
    LENGTH (FILTER I (MAP SND fields)) <= 3 /\
    EVERY (\f. if SND f then supported_event_leaf_type (SND (FST f))
               else supported_nested_type supported_event_leaf_type
                      (LENGTH ts) ts (SND (FST f))) fields
Proof
  Cases_on `id` >> simp[] >> rpt strip_tac >>
  drule_then assume_tac contract_inv_type_env >>
  rename1 `ALOOKUP mods src = SOME ts` >>
  rename1 `supported_event_fields ts (NONE,name) = SOME fields` >>
  `MEM (EventDecl name fields) ts` by drule_then ACCEPT_TAC log_supported_event_member >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  `contract_namespaces_ok cx.in_deploy mods` by
    (qpat_assum `body_const_cells_agree_mods _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     drule_then ACCEPT_TAC check_contract_namespaces_ok) >>
  `event_decl_unique name ts` by
    (irule contract_namespaces_ok_event_decl_unique >> metis_tac[]) >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods /\
   ce.ce_event_info = build_event_info_mods (type_env_all_modules mods) mods (K NONE) /\
   supported_module_headers ts` by
    (fs[contract_inv_def] >> qpat_assum `!src tops. ALOOKUP mods src = SOME tops ==> _`
       (drule_then (strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  qexistsl [`ts`,`fields`,`event_hash (get_tenv cx) name (MAP (SND o FST) fields)`] >>
  simp[lookup_event_metadata_def, lookup_event_metadata_in_decl] >>
  conj_tac
  >- (qmatch_goalsub_abbrev_tac `SOME data` >>
      DEP_REWRITE_TAC[Q.INST [`info` |-> `data`] log_event_mods_fold] >>
      simp[] >> reverse conj_tac
      >- (qexistsl [`src`,`ts`,`name`,`fields`] >> simp[]) >>
      rpt strip_tac >> rename1 `MEM (src',ts') mods` >>
      rename1 `MEM (EventDecl name' fs) ts'` >>
      `!s tops n f. MEM (s,tops) mods /\ MEM (EventDecl n f) tops ==> ~MEM #"." n` by
        (rpt gen_tac >> strip_tac >>
         qpat_assum `contract_namespaces_ok _ _`
           (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
         qpat_assum `EVERY (\(_,xs). EVERY _ xs) mods`
           (mp_tac o REWRITE_RULE [EVERY_MEM, FORALL_PROD]) >>
         disch_then (qspec_then `(s,tops)` mp_tac) >> simp[] >>
         disch_then (qspec_then `EventDecl n f` mp_tac) >> simp[]) >>
      `(src',name') = (src,name)` by
        (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
      gvs[] >>
      `ALOOKUP mods src = SOME ts'` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
      `ts' = ts` by fs[] >> gvs[event_decl_unique_def] >> metis_tac[]) >>
  fs[supported_module_headers_def, EVERY_MEM] >>
  qpat_assum `!e. MEM e ts ==> supported_module_declaration_header ts e`
    (qspec_then `EventDecl name fields` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
    [supported_module_declaration_header_def, supported_declaration_header_def, EVERY_MEM]) >>
  simp[]
QED
