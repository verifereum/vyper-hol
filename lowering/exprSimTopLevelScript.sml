(* Top-level name cases share the unchanged raw simulation interface. *)
Theory exprSimTopLevel
Ancestors
  exprSimTopLevelStorage exprSimTopLevelUndecodable exprSimTopLevelImmutable
  exprSimTopLevelMissing exprSimDefs exprSimHypsDefs vyperState
  vyperTypeGlobalLookupSoundness

Theorem compile_toplevel_name_sim:
  !cenv ann nsid. expr_vv_ok cenv (TopLevelName ann nsid)
Proof
  rw[expr_vv_ok_def] >> PairCases_on `nsid` >>
  rename1 `TopLevelName ann (src, id)` >>
  Cases_on `get_module_code cx src`
  >- simp[compile_toplevel_no_module_sim] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule compile_toplevel_immutable_sim >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tvt v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                         evaluate_type (get_tenv cx) typ = SOME tvt /\
                         read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)`
  >- (gvs[] >> irule compile_toplevel_storage_vv_sim >> metis_tac[]) >>
  irule compile_toplevel_storage_undecodable_sim >> metis_tac[]
QED

