(* The selector-hit branch of linked default dispatch comes from a getter. *)
Theory defaultDispatchModsHit
Ancestors
  alist compileUnit e2eModsDefs entryDispatchProps list pair
  venomWfProps vyperABIEntries vyperInterpreter vyperTypeContract
  vyperTypeContractGetter

Theorem default_decl_signature_origin[local]:
  MEM ("__default__",tys) (abi_decl_signatures top) ==>
  is_public_getter_decl "__default__" top /\
  !src:num option. MEM (src,"__default__") (external_name_keys_toplevel src top)
Proof
  Cases_on `top` >> simp[abi_decl_signatures_def, is_public_getter_decl_def,
                          external_name_keys_toplevel_def]
  >~ [`FunctionDecl vis _ _ _ _ _ _ _ _`]
  >- (Cases_on `vis` >> simp[abi_decl_signatures_def] >>
      rw[abi_function_signatures_def, MEM_MAP] >> pairarg_tac >> gvs[]) >>
  Cases_on `v` >> simp[abi_decl_signatures_def, is_public_getter_decl_def,
                       external_name_keys_toplevel_def]
QED

Theorem default_signature_lookup_origin:
  source_typing_ok_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps "__default__") = SOME tops /\
  vyperInterpreter$lookup_function (ALOOKUP exps "__default__") "__default__" External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM ("__default__",tys) (abi_deployed_signatures mods exps) /\
  (MEM "__default__" (MAP FST exps) ==>
   ~MEM (NONE,"__default__")
     (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) (main_module mods)))) ==>
  lookup_raw_return_or_F (ALOOKUP exps "__default__") "__default__" External tops = F /\
  ?top. MEM top tops /\ MEM ("__default__",tys) (abi_decl_signatures top) /\
    is_public_getter_decl "__default__" top /\
    external_getter_tuple (ALOOKUP exps "__default__" ) top = SOME (mut,nr,args,([]:expr
      list),ret,fbody)
Proof
  simp[] >> qabbrev_tac `src = ALOOKUP exps "__default__"` >>
  strip_tac >>
  `ALL_DISTINCT (MAP FST exps) /\
   ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel src) tops))` by
    (fs[source_typing_ok_mods_def] >>
     metis_tac[check_contract_external_names_distinct,
               contract_keys_module_distinct, ALOOKUP_MEM]) >>
  `MEM ("__default__",tys) (abi_external_signatures tops)` by
    (qpat_x_assum `MEM _ (abi_deployed_signatures _ _)` mp_tac >>
     simp[abi_deployed_signatures_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     strip_tac
     >- (Cases_on `ALOOKUP mods NONE` >> gvs[] >>
         rename1 `ALOOKUP mods NONE = SOME main` >>
         `src = NONE` suffices_by (strip_tac >> gvs[]) >>
         simp[Abbr `src`, ALOOKUP_NONE] >> CCONTR_TAC >>
         `MEM (NONE,"__default__")
              (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) main))` by
           (fs[abi_external_signatures_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            metis_tac[default_decl_signature_origin]) >>
         fs[main_module_def]) >>
     rename1 `MEM p exps` >> PairCases_on `p` >> gvs[] >>
     Cases_on `ALOOKUP mods (SOME p1)` >> gvs[MEM_FILTER] >>
     `src = SOME p1` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >> gvs[]) >>
  fs[abi_external_signatures_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rename1 `MEM top tops` >>
  drule default_decl_signature_origin >> strip_tac >>
  `lookup_raw_return src "__default__" External tops = NONE` by
    metis_tac[public_getter_raw_return_none] >>
  simp[lookup_raw_return_or_F_def] >> qexists_tac `top` >> simp[] >>
  drule lookup_function_external_raw_cases >> strip_tac >> gvs[] >>
  rename1 `is_public_getter_decl "__default__" other` >>
  `MEM (src,"__default__") (external_name_keys_toplevel src other)` by
    (Cases_on `other` >> fs[is_public_getter_decl_def] >>
     Cases_on `v` >> gs[is_public_getter_decl_def, external_name_keys_toplevel_def]) >>
  `top = other` suffices_by (disch_then SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  irule (Q.ISPEC `external_name_keys_toplevel (src:num option)` all_distinct_flat_map_inj) >>
  qexistsl_tac [`tops`, `src`, `(src,"__default__")`] >> simp[] >>
  first_assum (qspec_then `src` ACCEPT_TAC)
QED
