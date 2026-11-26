Theory whitelistLinkedBodyCalls
Ancestors
  alist list pair pred_set finite_map supportedDecls supportedProgram vyperInterpreter
  vyperTypeContract vyperTypeContractContext vyperTypeContractStaticMaps
  vyperTypeCallGraph constSubstMods whitelistCheckerFnSigs
  whitelistLinkedBodyEnv whitelistLinkedBodyCallSites

Theorem checked_signature_decl[local]:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_fn_sigs (src,callee) = SOME sg ==>
  ?tops vis mut nr rr args dflts ss.
    ALOOKUP mods src = SOME tops /\
    MEM (FunctionDecl vis mut nr rr callee args dflts sg.ret_ty ss) tops /\
    lookup_callable_function mode callee tops =
      SOME (mut,nr,args,dflts,sg.ret_ty,ss)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >> metis_tac[]
QED

Theorem checked_signature_return[local]:
  check_contract mode layouts addr mods = SOME art /\
  FLOOKUP art.cta_fn_sigs k = SOME sg ==>
  sg.ret_ty = NoneT \/ assignable_type (type_env_all_modules mods) sg.ret_ty
Proof
  PairCases_on `k` >> strip_tac >>
  drule_all checked_signature_decl >> strip_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >> simp[check_toplevel_decl_def]
QED

Theorem checked_main_call_return[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  FLOOKUP art.cta_fn_sigs (NONE,callee) = SOME sg /\
  IS_SOME (supported_function_decl tops (NONE,callee) Internal) ==>
  ?mut nr rr args dflts ss.
    supported_function_decl tops (NONE,callee) Internal =
      SOME (mut,nr,rr,args,dflts,sg.ret_ty,ss)
Proof
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  PairCases_on `x` >> drule supportedProgramTheory.supported_internal_lookup >> strip_tac >>
  drule_all checked_signature_decl >> strip_tac >>
  gvs[lookup_callable_function_def] >> metis_tac[]
QED

(* Only a main constructor needs to drop unobserved signatures. The original
   runtime entry environment is then available unchanged for default checking. *)
Theorem linked_checked_body_calls:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  (mode ==> vis = Deploy) /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss ==>
  ?fs.
    (~mode \/ src <> NONE ==> fs = (function_entry_env art mods src vis args).fn_sigs) /\
    linked_body_calls_env tops src
      ((function_entry_env art mods src vis args) with fn_sigs := fs) /\
    IS_SOME (type_stmts ((function_entry_env art mods src vis args) with fn_sigs := fs)
      ret ss) /\
    IS_SOME (type_stmts ((function_entry_env art mods src vis args) with fn_sigs := fs)
      ret (subst_consts_stmts_mods (consts_env_mods mods) ss))
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `env = function_entry_env art mods src vis args` >>
  qabbrev_tac `ss' = subst_consts_stmts_mods (consts_env_mods mods) ss` >>
  qabbrev_tac `ks = if mode /\ src = NONE then
                    set (function_int_calls dflts ss) UNION set (int_calls_stmts ss')
                  else UNIV` >>
  `env.fn_sigs = art.cta_fn_sigs /\ env.type_defs = type_env_all_modules mods` by
    simp[Abbr `env`, function_entry_env_def, FOLDL_extend_local_args_static,
         artifact_env_def] >>
  `IS_SOME (type_stmts env ret ss) /\ IS_SOME (type_stmts env ret ss')` by
    fs[check_function_body_def, Abbr `env`, Abbr `ss'`] >>
  qexists_tac `DRESTRICT env.fn_sigs ks` >>
  conj_tac >- (Cases_on `mode` >> Cases_on `src` >> simp[Abbr `ks`, DRESTRICT_UNIV]) >>
  conj_tac
  >- (simp[linked_body_calls_env_def, FLOOKUP_DRESTRICT_SOME] >>
      conj_tac >- metis_tac[checked_signature_return] >>
      rpt gen_tac >> strip_tac >> PairCases_on `k` >> gvs[Abbr `ks`] >>
      irule checked_main_call_return >> reverse conj_tac
      >- metis_tac[] >>
      Cases_on `mode` >> gvs[Abbr `ss'`] >>
      metis_tac[linked_checked_main_call_internal]) >>
  `set (int_calls_stmts ss) SUBSET ks /\ set (int_calls_stmts ss') SUBSET ks` by
    (Cases_on `mode /\ src = NONE` >>
     simp[Abbr `ks`, function_int_calls_def, LIST_TO_SET_APPEND, SUBSET_DEF]) >>
  qpat_assum `set (int_calls_stmts ss) SUBSET ks`
    (mp_tac o MATCH_MP (cj 2 type_stmt_fn_sigs_restrict)) >>
  qpat_assum `set (int_calls_stmts ss') SUBSET ks`
    (mp_tac o MATCH_MP (cj 2 type_stmt_fn_sigs_restrict)) >>
  simp[optionTheory.IS_SOME_MAP]
QED
