Theory unitCandidateOrigin
Ancestors
  compileUnit compileVyper loweringShapeProps ctorDeployDefs constSubstMods constSubst list pair

(* The raw pool contributes only Internal declarations and imported Deploy
   declarations. Name provenance is all that ID separation needs. *)
Theorem raw_unit_candidate_origin:
  !mods m f. MEM (m,f) (unit_internal_fns mods ++ imported_ctors mods) ==>
  ?tops v mut nr rr args dflts ret ss.
    MEM (m,tops) mods /\ v <> External /\
    MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops
Proof
  Induct >- simp[unit_internal_fns_def, imported_ctors_def] >>
  qx_gen_tac `md` >> PairCases_on `md` >>
  simp[unit_internal_fns_def, imported_ctors_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MEM_APPEND, MEM_MAP] >> rpt gen_tac >> strip_tac
  >- (PairCases_on `f` >> gvs[fn_decl_name_def] >>
      qspec_then `md1` mp_tac classify_fold_internal >> simp[] >>
      metis_tac[vyperASTTheory.function_visibility_distinct])
  >- metis_tac[]
  >- (Cases_on `md0` >> Cases_on `ctor` >> gvs[] >>
      PairCases_on `f` >> gvs[] >>
      qspec_then `md1` mp_tac classify_functions_ctor_mem >>
      simp[classify_functions_def, subst_consts_fn_def, fn_decl_name_def] >>
      metis_tac[vyperASTTheory.function_visibility_distinct])
  >> metis_tac[]
QED

Theorem classified_unit_candidate_origin:
  classify_functions_unit mods exps = (exts,ints,fb,cf,ctors) /\
  MEM (m,f) (ints ++ ctors) ==>
  ?tops v mut nr rr args dflts ret ss.
    MEM (m,tops) mods /\ v <> External /\
    MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops
Proof
  simp[classify_functions_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM (m,g) _` >>
  `MEM (m,g) (unit_internal_fns mods ++ imported_ctors mods)` by
    simp[MEM_APPEND] >>
  drule raw_unit_candidate_origin >>
  PairCases_on `g` >>
  simp[fn_decl_name_def, subst_consts_fn_mods_def]
QED

Theorem classified_unit_candidate_ids_11:
  classify_functions_unit mods exps = (exts,ints,fb,cf,ctors) /\
  MEM (s,f) (ints ++ ctors) /\ MEM (m,g) (ints ++ ctors) /\
  build_func_ids_mods n mods (nsid_to_string (s,fn_decl_name f)) =
  build_func_ids_mods n mods (nsid_to_string (m,fn_decl_name g)) ==>
  nsid_to_string (s,fn_decl_name f) = nsid_to_string (m,fn_decl_name g)
Proof
  strip_tac >>
  `?tops v mut nr rr args dflts ret ss.
     MEM (s,tops) mods /\ v <> External /\
     MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops` by
    metis_tac[classified_unit_candidate_origin] >>
  `?tops v mut nr rr args dflts ret ss.
     MEM (m,tops) mods /\ v <> External /\
     MEM (FunctionDecl v mut nr rr (fn_decl_name g) args dflts ret ss) tops` by
    metis_tac[classified_unit_candidate_origin] >>
  irule build_func_ids_mods_11 >> metis_tac[]
QED
