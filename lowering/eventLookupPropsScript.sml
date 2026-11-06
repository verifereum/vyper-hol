(* Checked event table agrees with compiler event information. *)
Theory eventLookupProps
Ancestors
  compileVyper vyperTypeEventLookup vyperTypeContract vyperEvent
  vyperTypeEnvExtension finite_map alist list

Theorem checked_event_info_lookup:
  check_contract dep layouts addr [(NONE,tops)] = SOME art ==>
  build_event_info tenv tops (K NONE) name = lookup_event_metadata_in tenv name tops
Proof
  strip_tac >> irule build_event_info_empty_lookup_event_metadata_in >>
  drule check_contract_event_decl_unique >> simp[]
QED

Theorem checked_log_event_info:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\
  type_stmt env ret (Log (src,name) es) = SOME env' ==>
  src = NONE /\ ?fields.
    FLOOKUP env.event_fields (src,name) = SOME fields /\
    build_event_info tenv tops (K NONE) name =
      SOME (event_hash tenv name (MAP (SND o FST) fields),
            MAP (SND o FST) fields, MAP SND fields)
Proof
  rpt strip_tac >>
  `build_event_info tenv tops (K NONE) name = lookup_event_metadata_in tenv name tops`
    by metis_tac[checked_event_info_lookup] >>
  gvs[check_contract_def, AllCaseEqs(), type_log_inversion] >>
  drule single_module_event_fields >> strip_tac >> gvs[] >>
  irule lookup_event_metadata_in_decl >>
  metis_tac[contract_namespaces_ok_event_decl_unique, MEM]
QED
