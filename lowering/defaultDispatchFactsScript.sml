(* Raw dispatch facts: the selected signature, not its name, determines placement. *)
Theory defaultDispatchFacts
Ancestors sourceEntryCode runtimeBodyStartDefs checkedSelectorTableProps entryStateRel
  vyperCalldata compileVyper vyperABIEntries publicGetterProps list entryDispatchProps

Theorem default_dispatch_raw_cases:
  calldata_dispatch tops cd = SOME (name,vals) ==>
  ((LENGTH cd < 4 \/
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = NONE) /\
   EXISTS is_default_decl tops /\ name = "__default__" /\ vals = []) \/
  (?tys tvs.
    4 <= LENGTH cd /\
    FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
      (abi_external_signatures tops) = SOME (name,tys) /\
    OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
    4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
    calldata_decode_args cd tvs 0 = SOME vals)
Proof
  simp[calldata_dispatch_def] >>
  Cases_on `LENGTH cd < 4`
  >- (simp[] >> Cases_on `EXISTS is_default_decl tops` >> simp[]) >>
  simp[] >>
  Cases_on `FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops)`
  >- (simp[] >> Cases_on `EXISTS is_default_decl tops` >> simp[]) >>
  simp[] >>
  PairCases_on `x` >>
  Cases_on `OPT_MMAP (evaluate_type (type_env tops)) x1` >> simp[] >>
  Cases_on `LENGTH cd < 4 + SUM (MAP tv_abi_size x)` >> simp[] >>
  Cases_on `calldata_decode_args cd x 0` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem default_decl_signature_getter[local]:
  MEM ("__default__",tys) (abi_decl_signatures top) ==>
  ?mut nr rr args ds ret body.
    public_getter top = SOME (mut,nr,rr,"__default__",args,ds,ret,body) /\
    tys = MAP SND args
Proof
  Cases_on `public_getter top`
  >- (Cases_on `top` >>
      gvs[public_getter_def, abi_decl_signatures_def]
      >~ [`FunctionDecl vis _ _ _ _ _ _ _ _`]
      >- (Cases_on `vis` >> simp[abi_decl_signatures_def] >>
          IF_CASES_TAC >> simp[abi_function_signatures_def, MEM_MAP,
            pairTheory.FORALL_PROD])
      >> Cases_on `v` >> gvs[public_getter_def, abi_decl_signatures_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >> gvs[]) >>
  PairCases_on `x` >> drule public_getter_signature >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem default_signature_getter:
  MEM ("__default__",tys) (abi_external_signatures tops) ==>
  ?mut nr rr args ds ret body.
    MEM (mut,nr,rr,"__default__",args,ds,ret,body) (public_getters tops) /\
    tys = MAP SND args
Proof
  simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
  strip_tac >> gvs[] >> drule default_decl_signature_getter >> strip_tac >>
  simp[MEM_public_getters] >> metis_tac[]
QED

Theorem default_selected_source_args:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM ("__default__",tys) (abi_external_signatures tops) ==>
  tys = MAP SND args /\
  ?rr. MEM (mut,nr,rr,"__default__",args,([]:expr list),ret,fbody) (public_getters tops)
Proof
  strip_tac >>
  drule (INST_TYPE [alpha |-> ``:expr``] default_signature_getter) >> strip_tac >>
  drule_all public_getter_lookup_agrees >> gvs[] >> metis_tac[]
QED

Theorem default_selected_decode:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME ("__default__",tys) /\
  OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
  calldata_decode_args cd tvs 0 = SOME vals ==>
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH cd /\
  calldata_decode_args cd tvs 0 = SOME vals
Proof
  strip_tac >>
  `MEM ("__default__",tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all default_selected_source_args >> strip_tac >> gvs[]
QED

Theorem default_dispatch_decl[local]:
  EXISTS is_default_decl tops ==>
  ?mut nr rr args ds ret fbody.
    MEM (FunctionDecl External mut nr rr "__default__" args ds ret fbody) tops
Proof
  simp[EXISTS_MEM] >> strip_tac >> Cases_on `e` >>
  gvs[is_default_decl_def] >> Cases_on `f` >> gvs[is_default_decl_def] >>
  metis_tac[]
QED

Theorem default_fallback_lookup_decl:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  ?rr. MEM (FunctionDecl External mut nr rr "__default__" args [] ret fbody) tops
Proof
  strip_tac >> drule default_dispatch_decl >> strip_tac >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
     SOME (mut',nr',args',ds,ret',fbody')` by
    (irule lookup_function_external_unique_decl >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `FunctionDecl External mut' nr' rr "__default__" args' ds ret' fbody'` >>
     simp[vyperTypeContractTheory.external_name_keys_toplevel_def,
       vyperInterpreterTheory.lookup_function_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem default_fallback_no_args:
  source_typing_ok tops am tx /\
  EXISTS is_default_decl tops /\
  vyperInterpreter$lookup_function NONE "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  args = []
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_external_names_distinct] >>
  drule_all default_fallback_lookup_decl >> strip_tac >>
  metis_tac[nonreentrantEntryEquivTheory.source_typing_function_header,
    supportedNamesTheory.supported_fallback_no_arguments]
QED

Theorem default_decl_no_getter:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (FunctionDecl External mut nr rr "__default__" args ds ret fbody) tops ==>
  (!nr' m ty x. ~MEM (VariableDecl (Public nr') m "__default__" ty x) tops) /\
  (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b "__default__" kt vt x) tops)
Proof
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  `MEM (NONE,"__default__")
    (external_name_keys_toplevel (NONE:num option)
      (FunctionDecl External mut nr rr "__default__" args ds ret fbody))` by
    simp[vyperTypeContractTheory.external_name_keys_toplevel_def] >>
  `F` suffices_by simp[] >>
  drule venomFnInstsProofsTheory.all_distinct_flat_map_unique >>
  strip_tac >>
  first_x_assum (qspec_then `FunctionDecl External mut nr rr "__default__" args ds ret fbody` mp_tac) >>
  simp[vyperTypeContractTheory.external_name_keys_toplevel_def]
  >- (qexists_tac `VariableDecl (Public nr') m "__default__" ty x` >>
      simp[vyperTypeContractTheory.external_name_keys_toplevel_def]) >>
  qexists_tac `HashMapDecl (Public nr') b "__default__" kt vt x` >>
  simp[vyperTypeContractTheory.external_name_keys_toplevel_def]
QED
