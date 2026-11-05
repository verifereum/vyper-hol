(* Counted, memory-safe top-level name reads.  Storage, transient and
   immutable names compile to pointers with no instructions, so each case
   is S1's counted proof on an empty memory path. *)
Theory bodyToplevelMemory
Ancestors
  exprSimTopLevelStorage exprSimTopLevelUndecodable exprSimTopLevelImmutable
  exprSimTopLevelMissing exprSimTopLevelProps exprSimProps exprSimHypsDefs
  exprSimMemDefs gasOutcome gasSummary fragGasMode fragGasPathMem context
  loweringPosts
  bodyMemoryDefs exprSimLeaves exprSimHyps exprSimDefs exprLowering
  compileEnv fragExecMem venomState loweringSlice valueEncoding
  exprLoweringProps accountsRelProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTyping
  vyperValueOperation vyperStorageLayoutSafety vyperLookupStorage
  vyperTypeGlobalLookupSoundness vyperTypeInvariants vyperTypeEnv list

Theorem gas_marked_exec_mem_refl[local]:
  gas_marked_exec F (ctx,func) source (es,s0) [] res ee (OK s0) /\
  ~s0.vs_halted ==>
  gas_marked_exec T (ctx,func) source (es,s0) [] res ee (OK s0)
Proof
  rw[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules]
QED

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
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `storage_layout_safe cx` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, expr_type_def]) >>
  gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tvt))`, `es`, `OK s0`] >>
  conj_tac
  >- (match_mp_tac gas_marked_exec_mem_refl >> simp[] >>
      irule toplevel_storage_marked_exec >> simp[]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule toplevel_storage_value_post >> simp[]) >>
  irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[mk_ptr_def]
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
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
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
  drule_all toplevel_immutable_lookup >> strip_tac >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`, `es`, `OK s0`] >>
  conj_tac
  >- (match_mp_tac gas_marked_exec_mem_refl >> simp[] >>
      irule toplevel_immutable_marked_exec >> simp[] >> metis_tac[]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule toplevel_immutable_post >> simp[] >> metis_tac[]) >>
  irule vv_store_bound_nonmem >> simp[mk_ptr_def]
QED

Theorem compile_toplevel_no_module_sim_mem:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  metis_tac[missing_module_not_gas_admissible]
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

