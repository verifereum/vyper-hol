(* Code-free storage/transient value views; forcing is not certified here. *)
Theory bodyToplevelMemory
Ancestors
  loweringPosts
  bodyMemoryDefs exprSimLeaves exprSimHyps exprSimDefs exprLowering
  compileEnv fragExecMem venomState loweringSlice valueEncoding
  exprLoweringProps accountsRelProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTyping
  vyperValueOperation vyperStorageLayoutSafety vyperLookupStorage
  vyperTypeGlobalLookupSoundness vyperTypeInvariants vyperTypeEnv list

Theorem compile_toplevel_storage_vv_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >>
     gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  drule_all eval_expr_toplevel_storage >> strip_tac >> gvs[] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[frag_exec_mem_def, stmt_state_rel_def, state_rel_def] >>
      metis_tac[]) >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, expr_type_def] >>
  Cases_on `tr` >> simp[] >> strip_tac >> gvs[] >>
  irule frag_exec_mem_refl >> rpt strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, storage_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def, expr_type_def]
QED

Theorem compile_toplevel_storage_undecodable_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rpt strip_tac >> simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM] >>
  Cases_on `lookup_var_slot_from_layout cx tr src id_str` >>
  simp[raise_def, return_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> simp[raise_def, return_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
QED

Theorem compile_toplevel_immutable_sim_mem:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  `env_consistent env cx es /\ state_well_typed es /\
   well_typed_expr env (TopLevelName ann (src,id))` by
    fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_find_NONE_bare_global >> strip_tac >>
  `src = cenv.ce_module /\
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         !tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
              off + type_memory_size tv < dimword (:256)` by
    (fs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM] >>
  simp[get_immutables_def, get_address_immutables_def, lift_option_type_def,
       bind_def, return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >> simp[return_def, raise_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables cenv.ce_module imms) id` >>
  simp[return_def, raise_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  rename1 `FLOOKUP _ id = SOME tvv` >> PairCases_on `tvv` >>
  strip_tac >> gvs[] >>
  `evaluate_type (get_tenv cx) ann = SOME tvv0` by
    (fs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  `value_has_type tvv0 tvv1` by
    (fs[state_well_typed_def, EVERY_MEM] >>
     drule alistTheory.ALOOKUP_MEM >> strip_tac >> first_x_assum drule >>
     simp[imms_well_typed_def] >>
     qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac >>
     simp[get_source_immutables_def] >> CASE_TAC >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, expr_type_def] >> strip_tac >> gvs[] >>
  irule frag_exec_mem_refl >> rpt strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, immutable_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def, expr_type_def] >>
  qexistsl [`id`, `off`, `tvv0`, `tvv1`, `0`] >>
  simp[sub_layout_def, read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, bind_def,
       return_def, evaluate_subscripts_def, lift_sum_def]
QED

Theorem compile_toplevel_no_module_sim_mem:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM] >>
  strip_tac >> gvs[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem compile_toplevel_name_vv_sim_mem:
  !ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt strip_tac >> PairCases_on `nsid` >>
  rename1 `TopLevelName ann (src, id)` >>
  Cases_on `get_module_code cx src`
  >- simp[compile_toplevel_no_module_sim_mem] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule compile_toplevel_immutable_sim_mem >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tvt v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                         evaluate_type (get_tenv cx) typ = SOME tvt /\
                         read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)`
  >- (gvs[] >> irule compile_toplevel_storage_vv_sim_mem >> metis_tac[]) >>
  irule compile_toplevel_storage_undecodable_sim_mem >> metis_tac[]
QED

