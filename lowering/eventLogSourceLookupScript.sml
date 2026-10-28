(* TOP-LEVEL: checked Log statements resolve the same event in the actual
   compiler environment and authoritative source table. Encoding equality
   includes the source logger address and the complete event payload. *)
Theory eventLogSourceLookup
Ancestors
  eventLookupProps compileVyper compileEnv vyperTypeEventLookup
  vyperTypeContract vyperTypeSystem vyperEvent vyperContext alist list

Theorem build_compile_env_event_tables:
  !tops vis mut name args ret body transient_locks.
    (build_compile_env tops vis mut name args ret body transient_locks).ce_event_info =
      build_event_info (type_env tops) tops (K NONE) /\
    (build_compile_env tops vis mut name args ret body transient_locks).ce_type_env = type_env tops
Proof
  rpt gen_tac >> simp[build_compile_env_def, LET_THM] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem checked_log_source_lookup:
  !tops dep layouts addr art env ret event_id exprs env' sources target cenv.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    ALOOKUP sources target = SOME [(NONE,tops)] /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) ==>
    cenv.ce_event_info (nsid_to_string event_id) =
      lookup_event_metadata (type_env tops) sources target event_id
Proof
  rpt gen_tac >> strip_tac >> Cases_on `event_id` >>
  rename1 `type_stmt env ret (Log (src,name) exprs) = SOME env'` >>
  `build_event_info (type_env tops) tops (K NONE) name =
    lookup_event_metadata_in (type_env tops) name tops` by
    (irule checked_event_info_lookup >> goal_assum drule) >>
  drule_all_then (qspec_then `type_env tops` strip_assume_tac) checked_log_event_info >>
  gvs[nsid_to_string_def, lookup_event_metadata_def]
QED

Theorem checked_log_source_encoding:
  !tops dep layouts addr art env ret event_id exprs env' sources target cenv values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    ALOOKUP sources target = SOME [(NONE,tops)] /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) ==>
    encode_source_event (type_env tops) sources target event_id values =
      encode_vyper_event cenv.ce_event_info (type_env tops) target (nsid_to_string event_id) values
Proof
  rpt strip_tac >> drule_all checked_log_source_lookup >> DISCH_TAC >>
  simp[encode_source_event_def, encode_vyper_event_def]
QED

Theorem checked_log_metadata_source_encoding:
  !tops dep layouts addr art env ret event_id exprs env' sources target cenv metadata values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    ALOOKUP sources target = SOME [(NONE,tops)] /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME metadata ==>
    encode_source_event (type_env tops) sources target event_id values =
      encode_vyper_event_metadata (type_env tops) target metadata values
Proof
  rpt strip_tac >> drule_all_then (qspec_then `values` assume_tac) checked_log_source_encoding >>
  gvs[encode_vyper_event_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked source Log lookup and encoding: " ^ name)
  end) (DB.thms "eventLogSourceLookup")
