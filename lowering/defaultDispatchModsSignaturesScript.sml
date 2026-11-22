(* Forward provenance of the entries in the linked selector table. *)
Theory defaultDispatchModsSignatures
Ancestors
  compileUnit constSubstMods publicGetterProps checkedSelectorTableProps compileVyper
  vyperABIEntries list pair alist
Libs
  BasicProvers

Theorem full_external_signature[local]:
  !m n r name args ds ret stmts. name <> "__default__" ==>
  MEM (name,MAP SND args)
    (abi_decl_signatures (FunctionDecl External m n r name args ds ret stmts))
Proof
  rpt strip_tac >> simp[abi_decl_signatures_def, abi_function_signatures_def, MEM_MAP] >>
  qexists_tac `(args,LENGTH ds)` >> simp[abi_entries_member, TAKE_LENGTH_ID_rwt2] >>
  decide_tac
QED

Theorem folded_entry_signature[local]:
  !tops m n r name args ds ret stmts.
    MEM (m,n,r,name,args,ds,ret,stmts)
      (FST (FOLDR classify_function ([],[],NONE,NONE) tops)) ==>
    MEM (name,MAP SND args) (abi_external_signatures tops)
Proof
  Induct >> simp[abi_external_signatures_def] >> qx_gen_tac `top` >>
  simp[classify_function_external_component] >> Cases_on `top` >> simp[] >>
  every_case_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  metis_tac[full_external_signature, abi_external_signatures_def]
QED

Theorem exported_entry_signature[local]:
  !s m n r name args ds ret stmts src tops key.
  (!src top m n r name args (ds : expr list) ret stmts.
     public_getter_src src top = SOME (m,n,r,name,args,ds,ret,stmts) ==>
     abi_decl_signatures top = [(name,MAP SND args)]) /\
  MEM (s,(m,n,r,name,args,ds,ret,stmts)) (exported_fn src tops key) ==>
  name = key /\ MEM (name,MAP SND args) (abi_external_signatures tops)
Proof
  rpt gen_tac >> simp[exported_fn_def] >> pairarg_tac >> gvs[] >>
  Cases_on `FILTER (\f. fn_decl_name f = key) exts` >> gvs[]
  >- (Cases_on `FILTER (\g. fn_decl_name g = key)
       (FLAT (MAP (\t. case public_getter_src src t of
                         NONE => [] | SOME g => [g]) tops))` >> gvs[] >>
      strip_tac >> gvs[] >>
      qpat_assum `FILTER _ _ = _ :: _`
        (mp_tac o Q.AP_TERM `MEM (m,n,r,name,args,ds,ret,stmts)`) >>
      simp[MEM_FILTER, fn_decl_name_def, MEM_FLAT, MEM_MAP, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      rename1 `public_getter_src s top = SOME _` >>
      `abi_decl_signatures top = [(key,MAP SND args)]` by metis_tac[] >>
      simp[abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
      qexists_tac `abi_decl_signatures top` >>
      conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]) >>
  strip_tac >> gvs[] >>
  qpat_assum `FILTER _ _ = _ :: _`
    (mp_tac o Q.AP_TERM `MEM (m,n,r,name,args,ds,ret,stmts)`) >>
  simp[MEM_FILTER, fn_decl_name_def] >>
  metis_tac[folded_entry_signature, FST]
QED

Theorem exported_entries_signatures[local]:
  !exps mods s m n r name args ds ret stmts.
  (!src top m n r name args (ds : expr list) ret stmts.
     public_getter_src src top = SOME (m,n,r,name,args,ds,ret,stmts) ==>
     abi_decl_signatures top = [(name,MAP SND args)]) /\
  MEM (s,(m,n,r,name,args,ds,ret,stmts)) (exported_fns mods exps) ==>
  MEM (name,MAP SND args)
    (FLAT (MAP (\(key,src). case ALOOKUP mods (SOME src) of
                     NONE => []
                   | SOME tops => FILTER (\(fnm,tys). fnm = key)
                                      (abi_external_signatures tops)) exps))
Proof
  Induct >> simp[exported_fns_def] >> qx_gen_tac `exp` >> PairCases_on `exp` >>
  simp[exported_fns_def] >> rpt gen_tac >>
  Cases_on `ALOOKUP mods (SOME exp1)` >> simp[MEM_FILTER] >>
  rpt strip_tac >> metis_tac[exported_entry_signature]
QED

Theorem compiled_entry_deployed_signature:
  (!src top m n r name args (ds : expr list) ret stmts.
     public_getter_src src top = SOME (m,n,r,name,args,ds,ret,stmts) ==>
     abi_decl_signatures top = [(name,MAP SND args)]) /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,ics) /\
  MEM (s,(m,n,r,name,args,ds,ret,stmts)) exts ==>
  MEM (name,MAP SND args) (abi_deployed_signatures mods exps)
Proof
  simp[classify_functions_unit_def] >> pairarg_tac >> gvs[] >>
  strip_tac >> gvs[MEM_MAP, MEM_APPEND] >>
  simp[abi_deployed_signatures_def]
  >- (PairCases_on `y` >> gvs[subst_consts_fn_mods_def] >>
      metis_tac[exported_entries_signatures]) >>
  PairCases_on `f` >> gvs[subst_consts_fn_mods_def] >>
  disj1_tac >> Cases_on `ALOOKUP mods NONE` >> gvs[main_module_def, public_getters_def]
  >- metis_tac[folded_entry_signature, FST] >>
  gvs[MEM_public_getters, abi_external_signatures_def, MEM_FLAT, MEM_MAP] >>
  rename1 `public_getter top = SOME _` >>
  drule public_getter_signature >> strip_tac >>
  qexists_tac `abi_decl_signatures top` >>
  conj_tac >- (qexists_tac `top` >> simp[]) >> simp[]
QED
