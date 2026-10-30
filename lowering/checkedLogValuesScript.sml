(* TOP-LEVEL: successful checked Log arguments have the declared field
   types, including argument widening. These facts supply the native
   Log packer's field layouts and its ABI output-capacity proof. *)
Theory checkedLogValues
Ancestors
  eventLookupProps vyperEventSoundness vyperTypeEventLookup vyperTypeEnvExtension
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeContract vyperTypeSystem vyperTypeDefaults
  compileEnv compileVyper vyperContext vyperInterpreter vyperValue vyperAST
  list pair finite_map option combin

Theorem log_field_value_types[local]:
  !fts values tenv.
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) fts values ==>
    ?ftvs. LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) fts ftvs /\
      values_have_types ftvs values
Proof
  Induct_on `fts` >- (Cases_on `values` >> simp[values_have_types_LIST_REL]) >>
  rpt gen_tac >> Cases_on `values` >- simp[] >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `evaluate_type tenv field_ty = SOME field_tv` >>
  first_x_assum drule_all >> disch_then (qx_choose_then `ftvs` strip_assume_tac) >>
  qexists_tac `field_tv::ftvs` >> fs[values_have_types_LIST_REL]
QED

Theorem checked_log_declared_values:
  !tops dep layouts addr art env ret event_id exprs env' cenv sig_hash fts flags values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
    LIST_REL (\e v. ?tv. evaluate_type (type_env tops) (expr_type e) = SOME tv /\
      value_has_type tv v) exprs values ==>
    ?ftvs. LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
      values_have_types ftvs values
Proof
  rpt gen_tac >> strip_tac >> Cases_on `event_id` >>
  rename1 `type_stmt env ret (Log (src,name) exprs) = SOME env'` >>
  drule_all_then (qspec_then `type_env tops` strip_assume_tac) checked_log_event_info >>
  rename1 `FLOOKUP env.event_fields (src,name) = SOME fields` >>
  `art = build_contract_type_artifact dep [(NONE,tops)]` by
    fs[check_contract_def, AllCaseEqs()] >>
  `MEM (EventDecl name fields) tops` by
    (`FLOOKUP (build_contract_type_artifact dep [(NONE,tops)]).cta_event_fields
      (src,name) = SOME fields` by gvs[] >>
     drule single_module_event_fields >> simp[]) >>
  `EVERY (\((_,ty),indexed). assignable_type (type_env_all_modules [(NONE,tops)]) ty /\
    (indexed ==> event_indexable_type ty)) fields` by
    (`MEM ((NONE:num option),tops) [(NONE,tops)]` by simp[] >>
     drule_all check_contract_event_fields >> simp[]) >>
  `EVERY (\((_,ty),_). well_formed_type (type_env tops) ty) fields` by
    (fs[EVERY_MEM, FORALL_PROD, type_env_all_modules_def, type_env_def] >>
     rpt strip_tac >> rename1 `MEM ((field_name,field_ty),indexed) fields` >>
     qpat_x_assum `!a b c. MEM _ fields ==> _`
       (qspecl_then [`field_name`, `field_ty`, `indexed`] mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
     drule_all assignable_type_well_formed >> simp[]) >>
  `LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) exprs fields` by
    (fs[type_log_inversion] >> gvs[]) >>
  drule_all compatible_event_values >> DISCH_TAC >>
  irule log_field_value_types >> gvs[nsid_to_string_def]
QED

Theorem checked_log_evaluated_argument_types:
  !env cx es ret event_id exprs env' values es'.
    runtime_consistent env cx es /\ functions_well_typed cx /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    call_evaluation_safe cx (int_calls_exprs exprs) /\
    eval_exprs cx exprs es = (INL values,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
      value_has_type tv v) exprs values
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_exprs env exprs` by fs[type_log_inversion] >>
  fs[runtime_consistent_def] >>
  qspecl_then [`cx`, `exprs`, `env`, `es`, `INL values`, `es'`]
    mp_tac (cj 9 eval_all_type_sound_mutual) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp_tac (srw_ss()) [exprs_runtime_typed_def, value_runtime_typed_def] >> strip_tac >>
  rename1 `LIST_REL (\e tv. evaluate_type env.type_defs (expr_type e) = SOME tv) exprs field_tvs` >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >> rename1 `expr_type (EL index exprs)` >>
  qexists_tac `EL index field_tvs` >> simp[]
QED
