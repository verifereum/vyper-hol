(* Shared source and layout facts for top-level names. *)
Theory exprSimTopLevelProps
Ancestors
  exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv loweringStateRelDefs context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv
  vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTyping
  vyperValueOperation vyperTypeValues valueEncoding fragExec venomState
  vyperStorageLayoutSafety vyperLookupStorage

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];

Theorem eval_expr_toplevel_storage:
  !cx ann src id es res es' ts tr typ id_str slot tvt v.
    eval_expr cx (TopLevelName ann (src, id)) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    es' = es /\ ?tv. res = INL tv /\ read_result cx tv es = (INL v, es)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  rpt strip_tac >>
  gvs[read_result_def, read_place_def, return_def, bind_def]
QED

Theorem toplevel_storage_ce_vars:
  !cenv cx src id ts tr typ id_str slot.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  first_x_assum irule >> simp[var_decl_transient_def]
QED

Theorem toplevel_storage_slots_in_range:
  !cx es src id ts tr typ id_str slot tvt.
    contract_storage_well_formed cx es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt
Proof
  rpt strip_tac >>
  `declared_storage_region cx src id [] = SOME (tr, n2w slot, tvt)` by
    simp[declared_storage_region_def] >>
  irule contract_storage_well_formed_region >>
  simp[vyperStorageBackendTheory.get_storage_backend_eq] >> metis_tac[]
QED

Theorem toplevel_storage_read_decodes:
  !cx es src id ts tr typ id_str slot tvt.
    contract_storage_well_formed cx es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    ?v. read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)
Proof
  rpt strip_tac >>
  `declared_storage_region cx src id [] = SOME (tr, n2w slot, tvt)` by
    simp[declared_storage_region_def] >>
  `?storage. get_storage_backend cx tr es = (INL storage, es)` by
    (Cases_on `tr` >>
     simp[get_storage_backend_def, bind_def, return_def,
          get_transient_storage_def, get_accounts_def]) >>
  drule_all contract_storage_well_formed_region >> strip_tac >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  gvs[read_storage_slot_def, bind_def, lift_option_def, return_def,
      wordsTheory.w2n_n2w]
QED

Theorem toplevel_find_NONE_bare_global:
  !env cx st src id ty ts.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  rpt strip_tac >> drule_all TopLevelName_toplevel_vtypes_Type >> strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,id)`
  >- metis_tac[TopLevelName_nonbare_find_NONE_contradiction] >>
  drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]
QED

Theorem admissible_toplevel_storage_lookup:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  gas_admissible (eval_expr cx (TopLevelName ann (src, id))) expr_vv_res_ok es ==>
  ?slot tvt. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
             evaluate_type (get_tenv cx) typ = SOME tvt
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >>
  lookup_global_tac >>
  Cases_on `lookup_var_slot_from_layout cx tr src id_str` >>
  simp[raise_def, return_def, expr_vv_res_ok_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def, expr_vv_res_ok_def]
QED

Theorem missing_module_not_gas_admissible:
  get_module_code cx src = NONE ==>
  ~gas_admissible (eval_expr cx (TopLevelName ann (src,id)))
    expr_vv_res_ok es
Proof
  strip_tac >> rewrite_tac[gas_admissible_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  lookup_global_tac >> simp[expr_vv_res_ok_def]
QED
