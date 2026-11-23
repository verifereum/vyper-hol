(* A checked module's ABI method IDs cover its compiler selectors. *)
Theory whitelistCheckerSelectorProps
Ancestors
  list rich_list arithmetic pair option words sorting
  vyperAST vyperTypeContract vyperABIEntries vyperImportRefsProps
  publicGetterProps supportedNames selectorDispatch compileVyper
  contractABI entryDispatchProps vyperGetter constSubst

Theorem calldata_method_id_abi_method_id[local]:
  !bs. LENGTH bs = 4 ==>
       w2n (calldata_method_id bs) = FOLDL (\n b. 256 * n + w2n b) 0 bs
Proof
  rpt strip_tac >> gvs[LENGTH_EQ_NUM_compute] >>
  simp[calldata_method_id_def, w2n_n2w, dimword_def] >>
  `!x:word8. w2n x < 256` by
    (gen_tac >> assume_tac (INST_TYPE [alpha |-> ``:8``] w2n_lt) >> fs[dimword_8]) >>
  qmatch_goalsub_rename_tac
    `16777216 * w2n a + (65536 * w2n b + (256 * w2n c + w2n d))` >>
  `w2n a < 256 /\ w2n b < 256 /\ w2n c < 256 /\ w2n d < 256` by simp[] >>
  `16777216 * w2n a + (65536 * w2n b + (256 * w2n c + w2n d)) <
   115792089237316195423570985008687907853269984665640564039457584007913129639936`
    by simp[] >>
  simp[LESS_MOD]
QED

Theorem compute_selector_abi_method_id[local]:
  FST (compute_selector tenv fname tys) = abi_method_id tenv fname tys
Proof
  simp[compute_selector_def, abi_method_id_def] >>
  irule calldata_method_id_abi_method_id >> simp[function_selector_length]
QED

Theorem classify_function_fst[local]:
  !h acc. FST (classify_function h acc) =
    case h of
      FunctionDecl External mut nr rr fname fargs dflts ret fbody =>
        if fname = "__default__" then FST acc
        else (mut, nr, rr, fname, fargs, dflts, ret, fbody) :: FST acc
    | _ => FST acc
Proof
  rpt gen_tac >> PairCases_on `acc` >> Cases_on `h` >>
  simp[classify_function_def] >>
  BasicProvers.every_case_tac >> rw[]
QED



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
      simp[classify_function_fst, public_getter_def, abi_decl_signatures_def,
           selector_ids_append, build_selectors_def]
      >- (Cases_on `fname = "__default__"`
          >- (gvs[] >> metis_tac[]) >>
      simp[build_selectors_def, compute_selector_abi_method_id] >>
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
  simp[classify_function_fst] >>
  qmatch_goalsub_abbrev_tac `public_getter top` >>
  (namedCases_on `public_getter top` ["", "gfn"]
  >- (simp[selector_ids_append, build_selectors_def] >>
      qexists_tac `xs` >> simp[] >>
      metis_tac[sublist_append_include]) >>
  PairCases_on `gfn` >>
  drule public_getter_signature >> strip_tac >>
  simp[selector_ids_append, build_selectors_def,
       compute_selector_abi_method_id] >>
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
