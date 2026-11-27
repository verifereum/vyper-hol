Theory bodySelectedCheckedBodySupportEnvMods
Ancestors
  bodyInvExecutionProps bodyInvSplit bodyCallSupport bodyExprPreFacts
  supportedProgram supportedStmtTraverse supportedDecls
  whitelistLinkedBodyTypes whitelistLinkedBodyData whitelistLinkedBodyEnv
  whitelistLinkedBodyCallSites whitelistCheckerDecls whitelistCheckerFnSigs
  vyperTypeContractContext vyperTypeContractStaticMaps vyperTypeCallGraph
  vyperInterpreter vyperState vyperTypeSystem externalBodyWidths
  linkedBodyLoopCalls vyperTypeContract vyperContext
  constSubstMods finite_map pred_set alist list pair option

Theorem selected_main_source_raw_edge[local]:
  supported_program tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\ vis <> Deploy ==>
  !callee. MEM (NONE,callee) (int_calls_stmts ss) ==>
    IS_SOME (supported_function_decl tops (NONE,callee) Internal)
Proof
  strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_body_def, supported_function_body_def] >>
  strip_tac >>
  qpat_x_assum `body_stmts_safe _ _` mp_tac >>
  simp[body_stmts_safe_iff, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem selected_use_source_resolution[local]:
  contract_inv mods exps ctx ce cx ==>
  ALOOKUP cx.sources cx.txn.target = SOME mods /\ linked_body_calls_resolved mods cx
Proof
  simp[contract_inv_def]
QED

Theorem selected_main_deploy_raw_edge_mods:
  contract_inv mods exps ctx ce cx /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\ vis <> Deploy ==>
  !callee. MEM (NONE,callee) (int_calls_stmts ss) ==>
    IS_SOME (supported_function_decl tops (NONE,callee) Internal)
Proof
  strip_tac >>
  Cases_on `?ts. mods = [(NONE,ts)]`
  >- (drule_all contract_inv_supported_module >> strip_tac >>
      rpt strip_tac >> drule_all selected_main_source_raw_edge >> simp[]) >>
  drule_all_then assume_tac check_contract_main_module_allocated >>
  drule_then strip_assume_tac selected_use_source_resolution >>
  `context_function_live cx (NONE,name)` by
    (simp[context_function_live_def] >> irule module_allocated_function_live >>
     qexists_tac `tops` >> simp[]) >>
  `check_function_body_in_mode cx.in_deploy vis` by simp[check_function_body_in_mode_def] >>
  gen_tac >> strip_tac >>
  `MEM (NONE,callee) (function_int_calls dflts ss)` by simp[function_int_calls_def] >>
  `!ts. mods <> [(NONE,ts)]` by metis_tac[] >>
  qpat_x_assum `linked_body_calls_resolved mods cx`
    (mp_tac o REWRITE_RULE [linked_body_calls_resolved_def]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)) >>
  simp[EVERY_MEM] >> disch_then (qspec_then `NONE` mp_tac) >> simp[] >>
  disch_then (qspec_then `(NONE,callee)` mp_tac) >>
  simp[supported_linked_callee_def]
QED

Theorem selected_entry_formals_mods:
  let env = function_entry_env art mods src vis args in
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss ==>
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     MEM (id,ty) args /\ assignable_type env.type_defs ty)
Proof
  simp[check_function_body_def, params_ok_def, function_entry_env_var_types_fdom] >>
  strip_tac >> rpt gen_tac >>
  simp[function_entry_env_def, FOLDL_extend_local_args_static, artifact_env_def] >>
  strip_tac >> drule_all FOLDL_extend_local_args_var_types_range >> simp[] >>
  fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem selected_signature_decl[local]:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_fn_sigs (src,name) = SOME sg ==>
  ?tops vis mut nr rr args dflts ss.
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl vis mut nr rr name args dflts sg.ret_ty ss) tops /\
    lookup_callable_function mode name tops = SOME (mut,nr,args,dflts,sg.ret_ty,ss)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  fs[FLOOKUP_DRESTRICT_SOME] >>
  drule_all_then strip_assume_tac build_contract_type_artifact_fn_sigs_declared_sound >>
  metis_tac[]
QED

Theorem selected_signature_return[local]:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_fn_sigs k = SOME sg ==>
  sg.ret_ty = NoneT \/ assignable_type (type_env_all_modules mods) sg.ret_ty
Proof
  PairCases_on `k` >> strip_tac >> drule_all_then strip_assume_tac selected_signature_decl >>
  drule_all check_contract_toplevel_decl_MEM_checked >> simp[check_toplevel_decl_def]
QED

Theorem selected_main_signature_return[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  FLOOKUP art.cta_fn_sigs (NONE,callee) = SOME sg /\
  IS_SOME (supported_function_decl tops (NONE,callee) Internal) ==>
  ?mut nr rr args dflts ss.
    supported_function_decl tops (NONE,callee) Internal =
      SOME (mut,nr,rr,args,dflts,sg.ret_ty,ss)
Proof
  simp[IS_SOME_EXISTS] >> strip_tac >> PairCases_on `x` >>
  drule_then assume_tac supported_internal_lookup >>
  drule_all_then strip_assume_tac selected_signature_decl >>
  gvs[lookup_callable_function_def] >> metis_tac[]
QED

Theorem selected_observed_main_signature[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  FLOOKUP art.cta_fn_sigs (NONE,callee) = SOME sg /\
  MEM (NONE,callee) (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  (mode /\ vis <> Deploy ==>
    !f. MEM (NONE,f) (int_calls_stmts ss) ==>
      IS_SOME (supported_function_decl tops (NONE,f) Internal)) ==>
  IS_SOME (supported_function_decl tops (NONE,callee) Internal)
Proof
  strip_tac >> Cases_on `mode /\ vis <> Deploy`
  >- (drule checked_subst_consts_int_calls_mods >> strip_tac >>
      fs[] >> metis_tac[]) >>
  `(mode ==> vis = Deploy /\
      (MEM (NONE,callee) (function_int_calls dflts ss) \/
       MEM (NONE,callee) (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss))))` by
    (Cases_on `mode` >> fs[]) >>
  drule_all linked_checked_main_call_internal >> simp[]
QED

Theorem selected_source_slots[local]:
  supported_program tops /\ MEM tl tops ==>
  case tl of
    VariableDecl _ Storage _ _ slot => IS_SOME slot
  | VariableDecl _ Transient _ _ slot => IS_SOME slot
  | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
  | _ => T
Proof
  strip_tac >> drule_all supported_program_declaration >> strip_tac >>
  Cases_on `tl` >> fs[supported_declaration_header_def]
  >- (rename1 `MEM (VariableDecl _ m _ _ opt) _` >>
      Cases_on `m` >> Cases_on `opt` >> gvs[]) >>
  rename1 `MEM (HashMapDecl _ _ _ _ _ opt) _` >> Cases_on `opt` >> gvs[]
QED

Theorem selected_checker_assignable_globals[local]:
  check_contract mode layouts (addr:160 word) mods = SOME art ==>
  !k ty. FLOOKUP art.cta_bare_global_assignable k = SOME ty ==>
         FLOOKUP art.cta_bare_globals k = SOME ty
Proof
  strip_tac >> gen_tac >> PairCases_on `k` >> rpt strip_tac >>
  Cases_on `mode`
  >- (mp_tac (Q.INST [`sources` |-> `[(addr,mods)]`,
                      `tx` |-> `empty_call_txn with target := addr`]
               check_contract_bare_global_assignable_consistent_deploy) >>
      simp[] >> disch_then drule >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`sources` |-> `[(addr,mods)]`,
                  `tx` |-> `empty_call_txn with target := addr`]
               check_contract_bare_global_assignable_consistent_initial) >>
  simp[] >> disch_then drule >> strip_tac >> simp[]
QED

Theorem selected_checked_body_support_env_mods:
  let b = subst_consts_stmts_mods (consts_env_mods mods) ss in
  let env = function_entry_env art mods src vis args in
  let env_s = env with fn_sigs := DRESTRICT env.fn_sigs (set (int_calls_stmts b)) in
  check_contract mode layouts (addr:160 word) mods = SOME art /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  (src = NONE ==> supported_program tops) /\
  (mode /\ src = NONE /\ vis <> Deploy ==>
    !callee. MEM (NONE,callee) (int_calls_stmts ss) ==>
      IS_SOME (supported_function_decl tops (NONE,callee) Internal)) ==>
  linked_body_env tops src (type_env_all_modules mods) env_s /\
  IS_SOME (type_stmts env_s ret b)
Proof
  ntac 3 (CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV)) >> strip_tac >>
  qabbrev_tac `b = subst_consts_stmts_mods (consts_env_mods mods) ss` >>
  qabbrev_tac `env = function_entry_env art mods src vis args` >>
  qabbrev_tac `en = env with fn_sigs := DRESTRICT env.fn_sigs (set (int_calls_stmts b))` >>
  reverse conj_tac
  >- (simp[Abbr `en`, cj 2 type_stmt_fn_sigs_restrict, IS_SOME_MAP] >>
      qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o SIMP_RULE bool_ss [check_function_body_def, LET_THM]) >>
      simp[Abbr `env`, Abbr `b`]) >>
  drule_all_then assume_tac linked_checked_body_type_facts >>
  `en.type_defs = type_env_all_modules mods /\
   en.toplevel_vtypes = art.cta_toplevel_vtypes /\
   en.bare_globals = art.cta_bare_globals /\
   en.bare_global_assignable = art.cta_bare_global_assignable /\
   en.event_fields = art.cta_event_fields` by
    simp[Abbr `en`, Abbr `env`, function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static] >>
  `linked_body_data_env tops src en` by
    (drule linked_checked_data_env_from_slots >>
     disch_then (drule_at (Pat `ALOOKUP _ _ = SOME _`)) >>
     disch_then (qspec_then `en` mp_tac) >> simp[] >>
     impl_tac
     >- (conj_tac
         >- (rpt strip_tac >> `supported_program tops` by fs[] >>
             drule_all selected_source_slots >> simp[]) >>
         strip_tac >> fs[linked_body_type_facts_def]) >>
     simp[]) >>
  simp[linked_body_env_def] >> rpt conj_tac
  >- (simp[Abbr `en`, Abbr `env`] >>
      drule (SIMP_RULE bool_ss [LET_THM] selected_entry_formals_mods) >>
      simp[function_entry_env_def, FOLDL_extend_local_args_static, artifact_env_def] >>
      metis_tac[])
  >- (simp[linked_body_calls_env_def, Abbr `en`, Abbr `env`,
           function_entry_env_fn_sigs, DRESTRICT_DEF, FLOOKUP_DRESTRICT_SOME] >>
      reverse conj_tac
      >- (rpt gen_tac >> strip_tac >> PairCases_on `k` >> gvs[] >>
          `IS_SOME (supported_function_decl tops (NONE,k1) Internal)` by
            (fs[Abbr `b`] >> drule_all selected_observed_main_signature >> simp[]) >>
          drule_all selected_main_signature_return >> simp[]) >>
      rpt strip_tac >> drule_all selected_signature_return >> simp[]) >>
  drule selected_checker_assignable_globals >> simp[]
QED

Theorem selected_checked_vtype_well_formed[local]:
  !tenv vt. check_value_type tenv vt ==> well_formed_vtype tenv vt
Proof
  Induct_on `vt` >>
  simp[check_value_type_def, well_formed_vtype_def, assignable_type_well_formed]
QED

(* The signature restriction does not alter any lookup used by the width check. *)
Theorem selected_checked_entry_widths_mods:
  linked_body_env tops src tenv (env with fn_sigs := sigs) /\
  type_stmts env ret b = SOME env' ==>
  ~supported_stmts_expr_exists (\e. ~byte_widths_expr e) b
Proof
  strip_tac >>
  qpat_assum `linked_body_env _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [linked_body_env_def]) >>
  irule type_stmts_excludes_bad_widths >>
  qexistsl_tac [`env`,`env'`,`ret`] >> simp[] >> conj_tac
  >- metis_tac[assignable_type_well_formed] >>
  qpat_x_assum `linked_body_data_env _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [linked_body_data_env_def]) >>
  metis_tac[selected_checked_vtype_well_formed]
QED
