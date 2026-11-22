Theory dispatchedSignatureLookupMods
Ancestors
  compileUnit defaultDispatchModsGetter dispatchedSignatureOriginMods
  entryDispatchProps list
  venomFnInstsProofs vyperABIEntries vyperTypeContract vyperTypeContractGetter
Libs
  BasicProvers

Theorem selected_decl_lookup_args:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops)) /\
  MEM top tops /\ MEM (name,tys) (abi_decl_signatures top) /\
  vyperInterpreter$lookup_function src name External tops =
    SOME (mut,nr,args,[],ret,b) ==>
  tys = MAP SND args /\
  ((name <> "__default__" /\
    ?rr. top = FunctionDecl External mut nr rr name args [] ret b) \/
   public_getter_src src top = SOME (mut,nr,F,name,args,([]:expr list),ret,b))
Proof
  strip_tac >>
  `MEM (src,name) (external_name_keys_toplevel src top)` by
    metis_tac[dispatchedSignatureOriginModsTheory.abi_decl_signature_external_key] >>
  drule lookup_function_external_raw_cases >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (`top = FunctionDecl External mut nr rr name args [] ret b` by
        (drule all_distinct_flat_map_unique >> disch_then irule >>
         simp[external_name_keys_toplevel_def]) >>
      Cases_on `name = "__default__"` >> gvs[abi_decl_signatures_def] >>
      metis_tac[]) >>
  `public_getter_src src decl = SOME (mut,nr,F,name,args,([]:expr list),ret,b)` by
    simp[tagged_getter_source_tuple] >>
  `MEM (src,name) (external_name_keys_toplevel src decl)` by
    (drule tagged_getter_name_key >> simp[fn_decl_name_def]) >>
  `top = decl` by
    (drule all_distinct_flat_map_unique >> disch_then irule >> simp[] >>
     qexists_tac `(src,name)` >> simp[]) >>
  gvs[] >> drule tagged_getter_decl_signature >> strip_tac >> gvs[]
QED
