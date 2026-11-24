(* A checked module's ABI method IDs cover its compiler selectors. *)
Theory whitelistCheckerSelectorProps
Ancestors
  list rich_list arithmetic pair option words sorting
  vyperAST vyperTypeContract vyperABIEntries vyperImportRefsProps
  publicGetterProps supportedNames selectorDispatch compileVyper
  contractABI vyperGetter constSubst selectorCompilerProps checkedSelectorTableProps

Theorem selector_ids_append[local]:
  !fs gs. MAP FST (build_selectors tenv (fs ++ gs)) =
    MAP FST (build_selectors tenv fs) ++ MAP FST (build_selectors tenv gs)
Proof
  Induct >> simp[build_selectors_def] >>
  gen_tac >> PairCases_on `h` >> simp[build_selectors_def]
QED

Theorem selector_ids_subst[local]:
  !fs env. MAP FST (build_selectors tenv (MAP (subst_consts_fn env) fs)) =
    MAP FST (build_selectors tenv fs)
Proof
  Induct >> simp[build_selectors_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[subst_consts_fn_def, build_selectors_def]
QED


Theorem build_selectors_provenance[local]:
  !tops. ?xs.
    sublist xs (abi_external_method_ids tenv tops) /\
    PERM (MAP FST (build_selectors tenv
            (FST (FOLDR classify_function ([],[],NONE,NONE) tops))) ++
          MAP FST (build_selectors tenv (public_getters tops))) xs
Proof
  Induct
  >- simp[abi_external_method_ids_def, abi_external_signatures_def,
          build_selectors_def, public_getters_def, sublist_nil] >>
  simp[abi_external_method_ids_def, abi_external_signatures_def,
       public_getters_def] >>
  strip_tac >> gvs[abi_external_method_ids_def, abi_external_signatures_def] >>
  Cases_on `h`
  >- (qmatch_goalsub_rename_tac `FunctionDecl vis mut nr rr fname fargs dflts fret fbody` >>
      Cases_on `vis` >>
      simp[classify_function_external_component, public_getter_def, abi_decl_signatures_def,
           selector_ids_append, build_selectors_def]
      >- (Cases_on `fname = "__default__"`
          >- (gvs[] >> metis_tac[]) >>
      simp[build_selectors_def, compute_selector_method_id] >>
      qexists_tac `abi_method_id tenv fname (MAP SND fargs) :: xs` >>
      simp[] >>
      `sublist [abi_method_id tenv fname (MAP SND fargs)]
        (MAP (\(name,tys). abi_method_id tenv name tys)
          (abi_function_signatures fname fargs dflts))` by
        (irule sublist_member_sing >>
         simp[abi_function_signatures_def, MAP_MAP_o, MEM_MAP] >>
         qexists_tac `(fname,MAP SND fargs)` >> simp[] >>
         qexists_tac `(fargs,LENGTH dflts)` >>
         simp[abi_entries_member, TAKE_LENGTH_TOO_LONG]) >>
      metis_tac[sublist_append_pair, APPEND]) >> metis_tac[]) >>
  simp[classify_function_external_component] >>
  qmatch_goalsub_abbrev_tac `public_getter top` >>
  (namedCases_on `public_getter top` ["", "gfn"]
  >- (simp[selector_ids_append, build_selectors_def] >>
      qexists_tac `xs` >> simp[] >>
      metis_tac[sublist_append_include]) >>
  PairCases_on `gfn` >>
  drule public_getter_signature >> strip_tac >>
  simp[selector_ids_append, build_selectors_def,
       compute_selector_method_id] >>
  qexists_tac `abi_method_id tenv gfn3 (MAP SND gfn4) :: xs` >>
  simp[PERM_FUN_APPEND_CONS] >>
  simp[GSYM sublist_cons])
QED

Triviality supported_selectors_distinct_of_method_ids:
  ALL_DISTINCT (abi_external_method_ids (type_env tops) tops) ==>
  supported_selectors_distinct tops
Proof
  strip_tac >>
  qspec_then `tops` strip_assume_tac
    (Q.INST [`tenv` |-> `type_env tops`]
      (INST_TYPE [alpha |-> ``:expr``] build_selectors_provenance)) >>
  simp[supported_selectors_distinct_def, classify_functions_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[selector_ids_subst, selector_ids_append] >>
  drule_all sublist_ALL_DISTINCT >> strip_tac >>
  drule sortingTheory.ALL_DISTINCT_PERM >> strip_tac >>
  pop_assum (irule o iffRL) >> first_assum ACCEPT_TAC
QED

Theorem check_contract_module_selectors_distinct:
  check_contract deploy layouts addr mods = SOME art /\ MEM (src,tops) mods ==>
  supported_selectors_distinct tops
Proof
  strip_tac >> irule supported_selectors_distinct_of_method_ids >>
  drule_all check_contract_module_external_method_ids_distinct >> simp[]
QED
