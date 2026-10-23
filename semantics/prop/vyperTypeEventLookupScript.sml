(* Event-table lookup boundaries for checked contracts. *)
Theory vyperTypeEventLookup
Ancestors
  vyperTypeContract vyperTypeEnvExtension vyperEvent finite_map list alist

Theorem add_toplevel_event_fields_sound[local]:
  FLOOKUP (add_toplevel_static_maps dep src tl art).cta_event_fields key = SOME fields ==>
  FLOOKUP art.cta_event_fields key = SOME fields \/
  ?name. key = (src,name) /\ tl = EventDecl name fields
Proof
  Cases_on `tl` >> simp[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `v0` >> gvs[]) >>
  TRY (Cases_on `include_fn_sig dep f` >> gvs[]) >>
  TRY (Cases_on `key = (src,s)` >> gvs[]) >> metis_tac[]
QED

Theorem add_module_event_fields_sound[local]:
  !art. FLOOKUP (add_module_static_maps dep src tls art).cta_event_fields key = SOME fields ==>
  FLOOKUP art.cta_event_fields key = SOME fields \/
  ?name. key = (src,name) /\ MEM (EventDecl name fields) tls
Proof
  Induct_on `tls` >> gvs[add_module_static_maps_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (drule add_toplevel_event_fields_sound >> strip_tac >> metis_tac[])
  >> metis_tac[]
QED

Theorem add_contract_event_fields_sound[local]:
  !art. FLOOKUP
    (FOLDL (\art (src,tls). add_module_static_maps dep src tls art) art mods).cta_event_fields
    key = SOME fields ==>
  FLOOKUP art.cta_event_fields key = SOME fields \/
  ?src name tls. key = (src,name) /\ MEM (src,tls) mods /\ MEM (EventDecl name fields) tls
Proof
  Induct_on `mods` >> simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (drule add_module_event_fields_sound >> strip_tac >> metis_tac[])
  >> metis_tac[]
QED

Theorem build_contract_event_fields_sound:
  FLOOKUP (build_contract_type_artifact dep mods).cta_event_fields (src,name) = SOME fields ==>
  ?tls. MEM (src,tls) mods /\ MEM (EventDecl name fields) tls
Proof
  simp[build_contract_type_artifact_def] >>
  disch_then (mp_tac o MATCH_MP add_contract_event_fields_sound) >>
  simp[empty_contract_type_artifact_def]
QED

Theorem lookup_event_metadata_in_decl:
  event_decl_unique name tls /\ MEM (EventDecl name fields) tls ==>
  lookup_event_metadata_in tenv name tls =
    SOME (event_hash tenv name (MAP (SND o FST) fields),
          MAP (SND o FST) fields, MAP SND fields)
Proof
  Induct_on `tls` >- simp[] >>
  rpt strip_tac >>
  `event_decl_unique name tls` by
    (fs[event_decl_unique_def] >> metis_tac[]) >>
  Cases_on `h` >> fs[lookup_event_metadata_in_def] >>
  Cases_on `s = name` >> fs[] >>
  `l = fields` by (fs[event_decl_unique_def] >> metis_tac[]) >> simp[]
QED

Theorem checked_artifact_event_metadata:
  contract_namespaces_ok dep mods /\
  FLOOKUP (build_contract_type_artifact dep mods).cta_event_fields (src,name) = SOME fields ==>
  ?tls. ALOOKUP mods src = SOME tls /\
    lookup_event_metadata_in tenv name tls =
      SOME (event_hash tenv name (MAP (SND o FST) fields),
            MAP (SND o FST) fields, MAP SND fields)
Proof
  rpt strip_tac >> drule build_contract_event_fields_sound >> strip_tac >>
  qexists `tls` >> conj_tac
  >- (irule ALOOKUP_ALL_DISTINCT_MEM >>
      gvs[contract_namespaces_ok_def]) >>
  irule lookup_event_metadata_in_decl >>
  metis_tac[contract_namespaces_ok_event_decl_unique]
QED

Theorem checked_artifact_source_event_metadata:
  contract_namespaces_ok dep mods /\ ALOOKUP sources target = SOME mods /\
  FLOOKUP (build_contract_type_artifact dep mods).cta_event_fields (src,name) = SOME fields ==>
  lookup_event_metadata tenv sources target (src,name) =
    SOME (event_hash tenv name (MAP (SND o FST) fields),
          MAP (SND o FST) fields, MAP SND fields)
Proof
  strip_tac >> drule_all checked_artifact_event_metadata >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  simp[lookup_event_metadata_def]
QED

Theorem single_module_event_fields:
  FLOOKUP (build_contract_type_artifact dep [(NONE,tops)]).cta_event_fields
    (src,name) = SOME fields ==>
  src = NONE /\ MEM (EventDecl name fields) tops
Proof
  strip_tac >> drule build_contract_event_fields_sound >> simp[]
QED

Theorem function_entry_env_event_fields[simp]:
  (function_entry_env art mods src args).event_fields = art.cta_event_fields
Proof
  simp[function_entry_env_def] >>
  `!env. (FOLDL (\env (id,ty). extend_local env id ty T) env args).event_fields =
          env.event_fields` suffices_by simp[artifact_env_def] >>
  Induct_on `args` >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem artifact_env_event_fields[simp]:
  (artifact_env art mods src).event_fields = art.cta_event_fields
Proof
  simp[artifact_env_def]
QED

Theorem checked_single_module_log_source:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmt env ret (Log (src,name) es) = SOME env' /\
  ALOOKUP sources target = SOME [(NONE,tops)] ==>
  src = NONE /\ ?fields.
    FLOOKUP env.event_fields (src,name) = SOME fields /\
    lookup_event_metadata tenv sources target (src,name) =
      SOME (event_hash tenv name (MAP (SND o FST) fields),
            MAP (SND o FST) fields, MAP SND fields)
Proof
  simp[check_contract_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[type_log_inversion] >>
  drule single_module_event_fields >> strip_tac >> gvs[] >>
  irule checked_artifact_source_event_metadata >> simp[] >> metis_tac[]
QED
