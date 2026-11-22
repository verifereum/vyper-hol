(* A full-arity canonical call selects its singleton in the grouped table. *)
Theory groupedCanonicalLegacySelection
Ancestors
  groupedEntryPackage sourceEntrySelection finite_map vyperContext
  vyperTypeContract vyperABIEntries list rich_list words entryDispatchProps
  selectorCompilerProps selectorDispatch calldataSelectorProps constSubst
  constSubstCorrect checkedSelectorTableProps

Theorem checked_abi_signature_find[local]:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (name,tys) (abi_external_signatures tops) ==>
  FIND (\(n,ts). abi_method_id (type_env tops) n ts =
                 abi_method_id (type_env tops) name tys)
    (abi_external_signatures tops) = SOME (name,tys)
Proof
  strip_tac >>
  `type_env_all_modules [(NONE,tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  `ALL_DISTINCT (abi_external_method_ids (type_env tops) tops)` by
    metis_tac[check_contract_external_method_ids_distinct, MEM] >>
  qabbrev_tac `key = \(n,ts). abi_method_id (type_env tops) n ts` >>
  qabbrev_tac `sigs = abi_external_signatures tops` >>
  `ALL_DISTINCT (MAP key sigs)` by
    fs[abi_external_method_ids_def, Abbr `key`, Abbr `sigs`] >>
  `(\(n,ts). abi_method_id (type_env tops) n ts = abi_method_id (type_env tops) name tys) =
    (\x. key x = key (name,tys))` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD, Abbr `key`] >>
  pop_assum (pure_rewrite_tac o single) >>
  Cases_on `FIND (\x. key x = key (name,tys)) sigs` >> gvs[]
  >- (fs[mem2varBlockSimHelpersTheory.FIND_NONE_EVERY, EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]) >>
  drule venomInstTheory.FIND_MEM >> disch_tac >>
  drule venomInstTheory.FIND_P >> simp[] >> disch_tac >>
  fs[MEM_EL, EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> metis_tac[]
QED

Theorem grouped_canonical_legacy_selection:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  4 <= LENGTH cd /\
  MEM (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
    (FST (classify_functions tops)) /\
  ?pre post lbl z pkg.
    MAP (package_external_group tops target trans keys) (FST (classify_functions tops)) =
      pre ++ ExternalSingle (cd_selector cd,lbl,z) pkg::post /\
    EVERY (\group. case group of
      ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
    | ExternalDefaults _ es _ _ =>
        FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) es = NONE) pre /\
    lbl = "fn_" ++ tx.function_name /\
    pkg = set_external_package_target target (package_external_fn tops trans keys
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,
       subst_consts_stmts (module_consts_env tops []) fbody))
Proof
  strip_tac >> drule_all valid_vyper_call_selected_calldata >> strip_tac >>
  drule calldata_encodes_hits_selector >>
  simp[TAKE_LENGTH_ID_rwt, compute_selector_method_id, calldata_hits_selector_def,
       arithmeticTheory.GREATER_EQ] >>
  strip_tac >>
  `cd_selector cd = abi_method_id (type_env tops) tx.function_name (MAP SND args)` by
    simp[cd_selector_method_id] >>
  drule_all lookup_function_external_raw_member >>
  simp[subst_consts_fn_def, subst_consts_exprs_map] >> strip_tac >> simp[] >>
  `MEM (tx.function_name, MAP SND args)
      (FLAT (MAP (\(m,n,r,f,a,d,t,b). abi_function_signatures f a d)
        (FST (classify_functions tops))))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     goal_assum (drule_at Any) >> simp[]) >>
  pop_assum mp_tac >> rewrite_tac[classify_external_signatures] >>
  disch_then (assume_tac o REWRITE_RULE [MATCH_MP sortingTheory.PERM_MEM_EQ
    abi_signature_partition]) >>
  `FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME (tx.function_name, MAP SND args)` by
    (simp[] >> irule checked_abi_signature_find >> simp[] >> goal_assum (drule_at Any)) >>
  drule_all grouped_selected_legacy_entry_shape >>
  disch_then (qspecl_then [`trans`,`target`,`keys`]
    (qx_choosel_then [`pre`,`post`,`lbl`,`z`,`pkg`] strip_assume_tac)) >>
  qexistsl_tac [`pre`,`post`,`z`] >> fs[]
QED
