(* TOP-LEVEL: checker facts needed by the actual Log argument/topic boundary.
   The event table supplies declaration types; the compiler supplies argument
   layout types. No event whitelist premise is used. *)
Theory checkedLogMetadata
Ancestors
  vyperEventArgCompat
  eventLookupProps logArgumentTyping eventLoweringStructure compileVyper
  vyperTypeEventLookup vyperTypeEnvExtension vyperTypeContract vyperTypeSystem
  vyperTypeInvariants compileEnv list pair combin finite_map

Theorem event_fields_indexability[local]:
  !fields tenv.
    EVERY (\((_,ty),indexed). assignable_type tenv ty /\
      (indexed ==> event_indexable_type ty)) fields ==>
    LIST_REL (\flag ty. flag ==> event_indexable_type ty)
      (MAP SND fields) (MAP (SND o FST) fields)
Proof
  Induct_on `fields` >- simp[] >>
  rpt gen_tac >> rename1 `EVERY _ (event_field::fields)` >>
  PairCases_on `event_field` >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem checked_log_compiler_metadata:
  !tops dep layouts addr art env cx es cenv ret event_id exprs env' cs args cut sig_hash fts flags.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\
    env_consistent env cx es /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty) /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
    compile_log_eval_all cenv exprs cs = (args,cut) ==>
    well_typed_exprs env exprs /\ LENGTH flags = LENGTH args /\
    LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags fts
Proof
  rpt gen_tac >> strip_tac >> Cases_on `event_id` >>
  rename1 `type_stmt env ret (Log (src,name) exprs) = SOME env'` >>
  drule_all_then (qspec_then `type_env tops` strip_assume_tac) checked_log_event_info >>
  rename1 `FLOOKUP env.event_fields (src,name) = SOME fields` >>
  `art.cta_event_fields =
   (build_contract_type_artifact dep [(NONE,tops)]).cta_event_fields` by
    gvs[check_contract_def, AllCaseEqs()] >>
  `MEM (EventDecl name fields) tops` by
    (`FLOOKUP (build_contract_type_artifact dep [(NONE,tops)]).cta_event_fields
      (src,name) = SOME fields` by gvs[] >>
     drule single_module_event_fields >> simp[]) >>
  `EVERY (\((_,ty),indexed). assignable_type (type_env_all_modules [(NONE,tops)]) ty /\
    (indexed ==> event_indexable_type ty)) fields` by
    (`MEM ((NONE:num option),tops) [(NONE,tops)]` by simp[] >>
     drule_all check_contract_event_fields >> simp[]) >>
  `LIST_REL event_arg_compatible (MAP (SND o FST) fields) (MAP SND args)` by
    (qspecl_then [`env`, `cx`, `es`, `cenv`, `ret`, `(src,name)`, `exprs`, `env'`, `fields`, `cs`]
      mp_tac checked_log_compiler_argument_types >> simp[]) >>
  `LENGTH args = LENGTH exprs` by
    (qspecl_then [`cenv`, `exprs`, `cs`] mp_tac compile_log_eval_all_length >> simp[]) >>
  drule_all event_fields_indexability >> DISCH_TAC >>
  gvs[nsid_to_string_def, type_log_inversion]
QED
