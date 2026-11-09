(*
 * The pointer twin of S1's TopLevelName case: a storage, transient, immutable or constant read, which may copy into a fresh buffer.
 *
 * TOP-LEVEL:
 *   toplevel_expr_sim_ptr
 *)
Theory exprSimPtrTopLevel
Ancestors
  bodyPtrDefs exprSimHypsDefs vyperAST vyperInterpreter list
  exprSimPtrTopLevelViews exprSimPtrTopLevelForce exprSimPtrTopLevelStorageBranch
  exprSimPtrTopLevelImmutableBranch exprSimTopLevelImmutable exprSimTopLevelProps
  exprSimHyps exprSimProps exprSimUnwrapProps exprSimMemorySource

Theorem toplevel_immutable_aggregate_total_ptr[local]:
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  ~is_word_type ann ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> rw[expr_sim_ptr_def] >>
  `gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  drule_all toplevel_immutable_lookup >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es` by
    (irule compile_toplevel_immutable_aggregate_sim_ptr >> metis_tac[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_ptr_def] >> disch_then drule_all >> simp[]
QED

Theorem toplevel_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt gen_tac >> disch_tac >> reverse conj_tac
  >- (irule compile_toplevel_name_vv_sim_ptr >> metis_tac[]) >>
  Cases_on `is_word_type ann`
  >- (irule compile_toplevel_word_sim_ptr >> metis_tac[]) >>
  PairCases_on `nsid` >> rename1 `TopLevelName ann (src,id)` >>
  Cases_on `get_module_code cx src`
  >- (rw[expr_sim_ptr_def] >> drule forced_expr_admissible_raw >>
      metis_tac[missing_module_not_gas_admissible]) >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule toplevel_immutable_aggregate_total_ptr >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tv v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                        evaluate_type (get_tenv cx) typ = SOME tv /\
                        read_storage_slot cx tr (n2w slot) tv es = (INL v,es)`
  >- (gvs[] >> irule compile_toplevel_storage_aggregate_sim_ptr >> metis_tac[]) >>
  rw[expr_sim_ptr_def] >>
  `gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  `F` suffices_by simp[] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
QED
