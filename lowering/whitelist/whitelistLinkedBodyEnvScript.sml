Theory whitelistLinkedBodyEnv
Ancestors
  finite_map pair vyperTypeContract vyperTypeSystem vyperImportRefs
  supportedTypes supportedExprForms supportedDecls compileEnv

(* The linked map is used for all typing. Only types occurring in syntax
   with the source's reference discipline need support relative to tops. *)
Definition linked_body_type_facts_def:
  linked_body_type_facts tops src tenv <=>
    (!ty. assignable_type tenv ty /\
          (src = NONE \/ imported_type_refs_ok ty) ==>
          supported_place_type tops ty) /\
    (!k fields. FLOOKUP tenv k = SOME (StructArgs fields) ==>
                EVERY (assignable_type tenv o SND) fields /\
                (well_formed_type tenv (StructT k) ==> assignable_type tenv (StructT k))) /\
    (!k fields. src = NONE /\ FST k = NONE /\
                FLOOKUP tenv k = SOME (StructArgs fields) ==>
                supported_struct_fields tops k = SOME fields)
End

(* Qualified roots are resolved in the linked unit; an imported body
   cannot observe unqualified roots. Keep checker typing and the main-only
   compiler descriptor correspondence separate. *)
Definition linked_body_data_env_def:
  linked_body_data_env tops src env <=>
    (!k ty. FLOOKUP env.bare_globals k = SOME ty ==>
            FLOOKUP env.toplevel_vtypes k = SOME (Type ty)) /\
    (!k vt. FLOOKUP env.toplevel_vtypes k = SOME vt ==>
            check_value_type env.type_defs vt) /\
    (!k vt. src = NONE /\ FST k = NONE /\
            FLOOKUP env.toplevel_vtypes k = SOME vt ==>
            supported_place_root tops k /\
            case vt of
              Type ty => build_hashmap_info tops k = NONE /\
                (supported_storage_value tops k ty \/
                 supported_immutable_type tops k = SOME ty \/
                 supported_constant_type tops k = SOME ty)
            | HashMapT kt v => ?tr. build_hashmap_info tops k = SOME (tr,kt,v)) /\
    (!k ty. src = NONE /\ FST k = NONE /\
            FLOOKUP env.bare_global_assignable k = SOME ty ==>
            supported_place_root tops k /\
            supported_immutable_type tops k = SOME ty) /\
    (!k ty. src = NONE /\ FST k = NONE /\
            FLOOKUP env.bare_globals k = NONE /\
            FLOOKUP env.toplevel_vtypes k = SOME (Type ty) ==>
            supported_storage_value tops k ty) /\
    (!k fields. src = NONE /\ FST k = NONE /\
                FLOOKUP env.event_fields k = SOME fields ==>
                supported_event_fields tops k = SOME fields)
End

(* In deploy mode the caller can first restrict fn_sigs to observable keys.
   The main declaration records the exact return type used by array loops. *)
Definition linked_body_calls_env_def:
  linked_body_calls_env tops src env <=>
    (!k sg. FLOOKUP env.fn_sigs k = SOME sg ==>
            sg.ret_ty = NoneT \/ assignable_type env.type_defs sg.ret_ty) /\
    (!k sg. src = NONE /\ FST k = NONE /\ FLOOKUP env.fn_sigs k = SOME sg ==>
            ?mut nr rr args dflts ss.
              supported_function_decl tops k Internal =
              SOME (mut,nr,rr,args,dflts,sg.ret_ty,ss))
End

Definition linked_body_env_def:
  linked_body_env tops src tenv env <=>
    env.type_defs = tenv /\
    (!x ty. FLOOKUP env.var_types x = SOME ty ==> assignable_type tenv ty) /\
    linked_body_type_facts tops src tenv /\
    linked_body_data_env tops src env /\
    linked_body_calls_env tops src env /\
    (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
            FLOOKUP env.bare_globals k = SOME ty)
End

Theorem linked_body_env_extend_local:
  linked_body_env tops src tenv env /\ assignable_type tenv ty ==>
  linked_body_env tops src tenv (extend_local env x ty b)
Proof
  rw[linked_body_env_def, linked_body_data_env_def, linked_body_calls_env_def,
     extend_local_def, FLOOKUP_UPDATE] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem linked_body_env_defaults:
  linked_body_env tops src tenv env ==>
  linked_body_env tops src tenv (defaults_env env)
Proof
  simp[linked_body_env_def, linked_body_data_env_def, linked_body_calls_env_def,
       defaults_env_def] >> metis_tac[]
QED

Theorem linked_body_toplevel_place:
  linked_body_data_env tops src env /\ (src = NONE \/ FST k <> NONE) /\
  FLOOKUP env.toplevel_vtypes k = SOME vt ==>
  supported_place_root tops k /\ check_value_type env.type_defs vt
Proof
  rw[linked_body_data_env_def] >>
  Cases_on `FST k = NONE` >> gvs[supported_place_root_def] >> metis_tac[]
QED

Theorem linked_body_value_read:
  linked_body_env tops src tenv env /\ (src = NONE \/ FST k <> NONE) /\
  (src = NONE \/ imported_type_refs_ok ty) /\
  (FLOOKUP env.toplevel_vtypes k = SOME (Type ty) \/
   FLOOKUP env.bare_globals k = SOME ty) ==>
  (supported_storage_value tops k ty \/ supported_immutable_type tops k = SOME ty \/
   supported_constant_type tops k = SOME ty) /\ supported_place_type tops ty
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `linked_body_env _ _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [linked_body_env_def, linked_body_type_facts_def, linked_body_data_env_def]) >>
  `FLOOKUP env.toplevel_vtypes k = SOME (Type ty)` by metis_tac[] >>
  `assignable_type tenv ty` by
    (qpat_assum `!k vt. _ ==> check_value_type env.type_defs vt` drule >>
     simp[check_value_type_def]) >>
  `supported_place_type tops ty` by metis_tac[] >>
  simp[] >> Cases_on `FST k = NONE`
  >- (`src = NONE` by metis_tac[] >>
      qpat_assum `!k vt. _ ==> supported_place_root tops k /\ _` $
        qspecl_then [`k`, `Type ty`] mp_tac >> simp[]) >>
  simp[supported_storage_value_def, supported_storage_type_def,
       GSYM supported_place_type_def]
QED
