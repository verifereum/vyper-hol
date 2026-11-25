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
       return_def, raise_def, LET_THM, ignore_bind_def,
       record_storage_event_def];

Theorem eval_expr_toplevel_storage:
  !cx ann src id es res es' ts tr typ id_str slot tvt v.
    eval_expr cx (TopLevelName ann (src, id)) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    es' = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
    ?tv. res = INL tv /\ read_result cx tv es = (INL v, es)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  rpt strip_tac >>
  gvs[read_result_def, read_place_def, return_def, bind_def,
      ignore_bind_def, record_storage_event_def]
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

(* ===== Storage and transient array bases (array_slot_base) ===== *)

(* A name the compile environment places in storage or transient storage
   is a storage variable: not missing (that is an immutable, a bare global
   placed at an ImmutableLoc), not a constant, not a mapping. *)
Theorem array_slot_base_storage_decl:
  expr_sim_inv cenv cx env s /\ well_typed_expr env (TopLevelName ann (src,id)) /\
  ~const_name_root cx (TopLevelName ann (src,id)) /\
  array_slot_base cenv (TopLevelName ann (src,id)) /\
  get_module_code cx src = SOME ts ==>
  ?tr typ id_str. find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str)
Proof
  simp[allocLimitsTheory.array_slot_base_def, const_name_root_def] >> strip_tac >>
  `FLOOKUP env.bare_globals (src,id) = NONE` by
    (Cases_on `FLOOKUP env.bare_globals (src,id)` >> simp[] >>
     qpat_x_assum `expr_sim_inv _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
       (qspecl_then [`src`, `id`, `x`] mp_tac) >>
     impl_tac >- gvs[] >> strip_tac >>
     qpat_x_assum `option_CASE (FLOOKUP _ _) _ _` mp_tac >> simp[]) >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ann)` by
    gvs[well_typed_expr_def] >>
  Cases_on `find_var_decl_by_name id ts`
  >- (gvs[expr_sim_inv_def] >>
      metis_tac[TopLevelName_nonbare_find_NONE_contradiction]) >>
  PairCases_on `x` >> Cases_on `x0` >> simp[] >>
  fs[expr_sim_inv_def] >>
  metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]
QED

(* So it evaluates to a storage place, if to anything. *)
Theorem array_slot_base_eval_storage:
  expr_sim_inv cenv cx env s /\ well_typed_expr env e /\ ~const_name_root cx e /\
  array_slot_base cenv e /\ eval_expr cx e s' = (INL r,t) ==>
  ?tr slot vt. r = PlaceR (StoragePlace tr slot vt)
Proof
  strip_tac >>
  `?ann src id. e = TopLevelName ann (src,id)` by
    (Cases_on `e` >> fs[allocLimitsTheory.array_slot_base_def] >>
     rename1 `TopLevelName _ nsid` >> PairCases_on `nsid` >> simp[]) >>
  gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  Cases_on `get_module_code cx src` >> lookup_global_tac >>
  drule_all array_slot_base_storage_decl >> strip_tac >> simp[] >>
  Cases_on `lookup_var_slot_from_layout cx tr src id_str` >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[bind_def, raise_def, return_def, ignore_bind_def,
       record_storage_event_def] >>
  rpt strip_tac >> gvs[]
QED

(* And it compiles to a storage or transient pointer, never memory or code. *)
Theorem array_slot_base_compile_location:
  array_slot_base cenv e ==>
  vv_location (FST (compile_expr cenv ty e st)) <> SOME LocMemory /\
  vv_location (FST (compile_expr cenv ty e st)) <> SOME LocCode
Proof
  Cases_on `e` >> simp[allocLimitsTheory.array_slot_base_def] >> strip_tac >>
  BasicProvers.every_case_tac >> gvs[compile_expr_def, vv_location_def, mk_ptr_def]
QED
