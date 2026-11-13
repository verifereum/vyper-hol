Theory dispatchedSignatureArgs
Ancestors entryDispatchProps publicGetterProps e2eDefs vyperABIEntries
  vyperTypeContract list

Theorem signature_decl_external_key[local]:
  !top name tys.
  MEM (name,tys) (abi_decl_signatures top) ==>
  MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) top)
Proof
  Cases >> simp[abi_decl_signatures_def, external_name_keys_toplevel_def] >>
  rpt gen_tac
  >- (Cases_on `f` >>
      simp[abi_decl_signatures_def, external_name_keys_toplevel_def] >>
      Cases_on `s = "__default__"` >>
      gvs[abi_decl_signatures_def, abi_function_signatures_def, MEM_MAP] >>
      rpt strip_tac >> PairCases_on `y` >> gvs[]) >>
  Cases_on `v` >>
  simp[abi_decl_signatures_def, external_name_keys_toplevel_def]
QED

Theorem external_key_singleton_lookup[local]:
  !top name.
  MEM (NONE,name) (external_name_keys_toplevel (NONE:num option) top) ==>
  ?result. vyperInterpreter$lookup_function NONE name External [top] = SOME result
Proof
  Cases >> simp[external_name_keys_toplevel_def] >> rpt gen_tac
  >- (Cases_on `f` >> simp[external_name_keys_toplevel_def,
                         vyperInterpreterTheory.lookup_function_def]) >>
  Cases_on `v` >> simp[external_name_keys_toplevel_def,
                       vyperInterpreterTheory.lookup_function_def] >>
  rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dispatched_signature_args:
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (name,tys) (abi_external_signatures tops) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) ==> tys = MAP SND args
Proof
  rpt strip_tac >>
  gvs[source_typing_ok_def] >>
  drule check_contract_external_names_distinct >>
  simp[contract_keys_def] >> strip_tac >>
  qpat_x_assum `MEM _ (abi_external_signatures _)` mp_tac >>
  simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  drule signature_decl_external_key >> strip_tac >>
  drule external_key_singleton_lookup >> strip_tac >>
  drule_all lookup_function_external_unique_decl >> strip_tac >>
  gvs[] >>
  qpat_x_assum `lookup_function _ _ _ _ = _` kall_tac >>
  drule_then strip_assume_tac vyperTypeContractGetterTheory.lookup_function_External_cases >>
  gvs[]
  >- (gvs[abi_decl_signatures_def, abi_function_signatures_no_defaults] >>
      Cases_on `name = "__default__"` >> gvs[]) >>
  `public_getter decl = SOME (mut,F,F,name,args,([]:expr list),ret,fbody)` by
    (rewrite_tac[public_getter_source_tuple] >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  drule public_getter_signature >> strip_tac >> gvs[]
QED
