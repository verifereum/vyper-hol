(* The observed RHS place is live at its own endpoint, including when
   evaluating its index or popping its element changes the source state. *)
Theory bodySavedRhsSlotLiveMods
Ancestors
  bodyFullPostsMods bodySimModsProps bodyInvCodeProps bodyAugPlaceTarget
  bodyInvSplit targetPlaceSim compileEnv context vyperContext exprSimHypsDefs
  bodyFullAssign bodyMemSnapshotSourceLocation
  exprBodyPreTypingProps exprBodyPreCallSafetyProps exprPtrUnwrapStorageShape
  exprSimPopNestedBase exprReasonOperand assignEffectfulIndexCode
  compileVyper compileUnit supportedExprs exprCallBounds exprLowering
  loweringStateRelDefs loweringPosts vyperState vyperValue vyperInterpreter vyperAST
  vyperTypeSoundness vyperTypeExtCallCore vyperFiniteStoragePreservation
  vyperStorageFootprint vyperStoragePlaceObserved accountsRelProps vyperPlaceMutationSoundness
  vyperStorageBackend vyperTypeInvariants vyperTypeSystem vyperTypeExprSoundness
  finite_map words arithmetic option alist list pair

Theorem saved_observed_storage_read[local]:
  runtime_consistent env cx es /\ well_typed_expr env e /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  valid_horizon cx es H mid.storage_trace /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot leaf)),mid) ==>
  storage_read_live H tr raw slot leaf
Proof
  strip_tac >>
  Cases_on `type_slot_size leaf = 0`
  >- simp[storage_read_live_def, w2n_lt, LESS_IMP_LESS_OR_EQ] >>
  drule_all eval_expr_observed_region >> strip_tac >>
  `MEM (tr,n2w offset,tv) (FST H)` by
    (irule storage_observations_ok_root >> fs[valid_horizon_def] >> metis_tac[]) >>
  irule storage_place_observed_read_live >>
  simp[storage_place_observed_def] >>
  qexistsl [`n2w offset`, `tv`, `path`, `delta`] >> simp[]
QED

Theorem saved_slot_live_from_place[local]:
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,mid) raw (Type ty) /\
  vv_place_ptr_mods cenv cx mid s raw (LocatedValue ty p) /\
  (!v. raw <> Value v) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tr slot leaf. raw = PlaceR (StoragePlace tr slot leaf) ==>
     storage_read_live H tr (get_storage cx mid tr) slot leaf) ==>
  vv_storage_live H cx (LocatedValue ty p) mid s
Proof
  strip_tac >> Cases_on `raw` >> gvs[eval_result_typed_def] >>
  Cases_on `p'` >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, runtime_place_typed_def,
      place_type_value_def, slot_loc_def, vyperStateTheory.return_def] >>
  Cases_on `b` >> gvs[]
QED

Theorem saved_slot_location_src[local]:
  !tops owner vars src id loc.
    FLOOKUP (add_module_var_locations_src owner tops vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    (src = owner /\ find_var_decl_by_name id tops <> NONE)
Proof
  Induct >> simp[add_module_var_locations_src_def] >>
  Cases >> simp[add_module_var_locations_src_def, find_var_decl_by_name_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem saved_slot_location_modules[local]:
  !mods vars src id loc.
    ALL_DISTINCT (MAP FST mods) /\
    FLOOKUP (add_module_var_locations_mods mods vars) (src,id) = SOME loc ==>
    FLOOKUP vars (src,id) = SOME loc \/
    ?tops. ALOOKUP mods src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  Induct >> simp[add_module_var_locations_mods_def] >>
  PairCases >> simp[add_module_var_locations_mods_def] >>
  rename1 `MEM owner (MAP FST rest)` >> rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- (drule_then strip_assume_tac saved_slot_location_src >> simp[]) >>
  Cases_on `owner = src` >> gvs[] >>
  `ALOOKUP rest owner = NONE` by simp[ALOOKUP_NONE] >> gvs[]
QED

Theorem saved_slot_annotated_src[local]:
  !tops src vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_src src tops vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_src_def] >>
  Cases >> simp[add_annotated_immutables_src_def] >>
  rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> first_x_assum drule_all >>
  simp[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem saved_slot_annotated_modules[local]:
  !mods vars key loc.
    (!off. loc <> ImmutableLoc off) /\
    FLOOKUP (add_annotated_immutables_mods mods vars) key = SOME loc ==>
    FLOOKUP vars key = SOME loc
Proof
  Induct >> simp[add_annotated_immutables_mods_def] >>
  PairCases >> simp[add_annotated_immutables_mods_def] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >>
  drule_all_then ACCEPT_TAC saved_slot_annotated_src
QED

Theorem saved_slot_location_unit[local]:
  FLOOKUP (add_immutable_locations_unit sft mods vars) key = SOME loc /\
  (!off. loc <> ImmutableLoc off) ==>
  FLOOKUP vars key = SOME loc
Proof
  Cases_on `mods`
  >- simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
  rename1 `add_immutable_locations_unit _ (entry::rest) _` >>
  Cases_on `rest` >> PairCases_on `entry` >>
  rename1 `add_immutable_locations_unit _ ((owner,_)::_) _` >>
  Cases_on `owner` >> simp[add_immutable_locations_unit_def] >>
  rpt strip_tac >>
  metis_tac[add_immutable_locations_FLOOKUP, saved_slot_annotated_modules]
QED

Theorem saved_slot_source_decl[local]:
  contract_inv mods exps ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME loc /\
  ((?slot. loc = StorageLoc slot) \/ (?slot. loc = TransientLoc slot)) ==>
  ?tops. get_module_code cx src = SOME tops /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  `!off. loc <> ImmutableLoc off` by fs[] >>
  `ALL_DISTINCT (MAP FST mods) /\ cenv.ce_module_vars =
     add_immutable_locations_unit
       (get_struct_fields (make_struct_fields_map_mods mods)) mods
       (add_module_var_locations_mods mods FEMPTY)` by
    fs[contract_inv_def, cenv_module_pins_mods_def] >>
  qpat_assum `cenv.ce_module_vars = _` (fn eq =>
    qpat_assum `FLOOKUP cenv.ce_module_vars _ = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all_then assume_tac saved_slot_location_unit >>
  drule_all_then strip_assume_tac saved_slot_location_modules >> gvs[] >>
  drule_all contract_inv_module_codes >> simp[]
QED

Theorem saved_slot_target_root[local]:
  !bt f cenv sa op loc pt sb mods exps ctx cx.
    contract_inv mods exps ctx cenv cx /\
    compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    ~immutable_root cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_get_target_ptr_def, LET_THM] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `?tops. get_module_code cx p0 = SOME tops /\ find_var_decl_by_name p1 tops <> NONE` by
        (irule saved_slot_source_decl >> metis_tac[]) >>
      gvs[immutable_root_def, target_root_def]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  PairCases_on `result` >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  metis_tac[immutable_root_def, target_root_def]
QED

Theorem saved_pop_place_nonvalue[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  pop_place cx p es = (INL raw,mid) ==> !v. raw <> Value v
Proof
  Cases_on `p` >> simp[] >> strip_tac
  >~ [`pop_place _ (MemoryPlace _ _) _ = _`]
  >- (drule pop_memory_place_success >> strip_tac >> gvs[]) >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  Cases_on `t` >> simp[pop_place_def, raise_def] >>
  rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
  simp[pop_place_def, raise_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem saved_slot_pop_nonvalue[local]:
  contract_inv mods exps ctx cenv cx /\
  compile_expr cenv ty (Pop ann bt) sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx (Pop ann bt) es = (INL raw,mid) ==>
  !v. raw <> Value v
Proof
  strip_tac >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `loc_opt` >> simp[mk_ptr_def] >> strip_tac >> gvs[] >>
  `~immutable_root cx bt` by (irule saved_slot_target_root >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `!src id path. p <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> rename1 `get_place pv _ = _` >>
     Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
     metis_tac[aug_place_base_immutable_origin]) >>
  irule saved_pop_place_nonvalue >> metis_tac[]
QED

Theorem saved_global_nonvalue[local]:
  eval_expr cx (TopLevelName ann (src,id)) es = (INL raw,mid) ==>
  !v. raw <> Value v
Proof
  simp[Once evaluate_def, lookup_global_def] >>
  Cases_on `get_module_code cx src` >> simp[bind_def, lift_option_type_def, raise_def] >>
  Cases_on `find_var_decl_by_name id x` >>
  gvs[bind_def, return_def, raise_def, get_immutables_def, AllCaseEqs()]
  >- (rpt strip_tac >> gvs[] >>
      rename1 `(case FLOOKUP fm id of NONE => _ | SOME _ => _) _ = _` >>
      Cases_on `FLOOKUP fm id` >> gvs[return_def, raise_def]) >>
  PairCases_on `x'` >> Cases_on `x'0` >>
  simp[bind_def, ignore_bind_def, lift_option_type_def,
       return_def, raise_def, record_storage_event_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Only place-forming expressions can leave a slot pointer in the VV. *)
Theorem saved_slot_expr_cases[local]:
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  (case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)
Proof
  disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  Cases_on `e` >> simp[] >>
  pure_once_rewrite_tac [cj 1 compile_expr_raw_def]
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_literal) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_ifexp) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_structlit) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Call _ _ _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_call) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- suspend "builtin"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >- suspend "typebuiltin" >>
  simp[compile_expr_body_def, expr_type_def, compile_name_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def, AllCaseEqs()] >>
  rename1 `FLOOKUP cenv.ce_vars nm` >>
  Cases_on `FLOOKUP cenv.ce_vars nm`
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])) >>
  rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Resume saved_slot_expr_cases[builtin]:
  disch_then (mp_tac o MATCH_MP reason_compile_expr_builtin_shape_classify) >>
  gvs[reason_result_shape_def] >>
  (simp[exprCallBoundsTheory.builtin_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ bi _ _` >>
  Cases_on `bi` >> strip_tac
  >~ [`Acc item`] >- suspend "acc"
  >~ [`AsWeiValue denom`] >- suspend "wei"
  >~ [`Len`] >- (drule reason_builtin_len >> gvs[reason_result_shape_def])
  >~ [`Bop bop`] >- (drule reason_builtin_bop >> gvs[reason_result_shape_def])
  >~ [`MakeArray et bd`] >- (drule reason_builtin_makearray >> gvs[reason_result_shape_def])
  >~ [`MethodId`] >- (drule reason_builtin_method_id >> gvs[reason_result_shape_def])
  >~ [`Keccak256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
  >~ [`Sha256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
  >~ [`CalldataSlice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
  >~ [`ECAdd`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
  >~ [`ECMul`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
  >~ [`Concat n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
  >~ [`Slice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
  >~ [`Uint2Str n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def]) >>
  drule_at Any reason_builtin_scalar >> simp[reason_result_shape_def])
QED

Resume saved_slot_expr_cases[typebuiltin]:
  simp[compile_expr_body_def, expr_type_def] >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  rename1 `compile_type_builtin_dispatch_body _ _ _ _ tb _ _ _` >>
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def, base_ptr_def]
QED

Resume saved_slot_expr_cases[acc]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def, AllCaseEqs()]
QED

Resume saved_slot_expr_cases[wei]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), oneline as_stack_val_def]
QED

Finalise saved_slot_expr_cases[local]

Theorem saved_slot_result_nonvalue[local]:
  !e ty sa t p sb es raw mid.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL raw,mid) ==> !v. raw <> Value v
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `case e of TopLevelName _ _ => T | Pop _ _ => T |
       Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F` by
    (drule_all_then ACCEPT_TAC saved_slot_expr_cases) >>
  Cases_on `e` >> gnvs[]
  >~ [`TopLevelName _ _`] >-
    (rename1 `eval_expr cx (TopLevelName ann key) _ = _` >> PairCases_on `key` >>
     drule saved_global_nonvalue >> simp[])
  >~ [`Pop _ _`] >- (drule_all saved_slot_pop_nonvalue >> simp[]) >>
  `p.ptr_location <> LocMemory` by fs[]
  >~ [`Subscript _ _ _`] >- suspend "subscript" >>
  suspend "attribute"
QED

Resume saved_slot_result_nonvalue[subscript]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_all body_assign_subscript_storage_origin >> simp[] >> strip_tac >>
  `~subscript_reads_base cx e' e0` by metis_tac[body_inv_copies_subscript_base_mods] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >> gvs[vv_location_def] >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (drule_then assume_tac) >>
  `!v. res <> Value v` by metis_tac[] >>
  metis_tac[body_assign_select_nonvalue]
QED

Resume saved_slot_result_nonvalue[attribute]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_all body_assign_attribute_storage_origin >> simp[] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `compile_expr cenv ty e' sa` >> Cases_on `q` >> gvs[vv_location_def] >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (drule_then assume_tac) >>
  `!v. res <> Value v` by metis_tac[] >>
  metis_tac[body_assign_select_nonvalue]
QED

Finalise saved_slot_result_nonvalue[local]

(* The same horizon is used for the prefix and the reached RHS. Its
   entry well-formedness comes from the prefix resource of the raw run. *)
Theorem saved_rhs_slot_live_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  storage_well_formed_on cx es (FST H) /\
  valid_horizon cx st0 H mid.storage_trace /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL v,mid) /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 mid raw vv s ==>
  vv_storage_live H cx vv mid s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vv` >- simp[] >> rename1 `LocatedValue ty p` >>
  reverse (Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`)
  >- fs[] >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `runtime_consistent env cx (es with gas_obs := gs)` by
    fs[runtime_consistent_def] >>
  `(storage_well_formed_on cx (es with gas_obs := gs) (FST H) <=>
    storage_well_formed_on cx es (FST H))` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `valid_horizon cx (es with gas_obs := gs) H mid.storage_trace` by
    fs[valid_horizon_def] >>
  `eval_result_typed (env,cx,mid) raw (Type (expr_type e))` by
    (drule_at (Pat `eval_expr _ _ _ = _`) typed_expr_success_preserves_type >>
     fs[runtime_consistent_def] >> disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `env.type_defs = get_tenv cx` by metis_tac[runtime_consistent_get_tenv] >>
  `vv_place_ptr_mods cenv cx mid s raw (LocatedValue ty p) /\
   vv_holds_mods cenv cx (post_value_type cenv e) raw (LocatedValue ty p) mid s` by
    fs[vv_post_mods_def] >>
  `post_value_type cenv e = expr_type e` by
    (drule_all compile_storage_lowered_value_type >> simp[post_value_type_lowered]) >>
  `ty = expr_type e` by (Cases_on `p.ptr_location` >> gvs[vv_holds_mods_def, vv_holds_def]) >>
  `!v. raw <> Value v` by (drule_all saved_slot_result_nonvalue >> simp[]) >>
  qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  irule saved_slot_live_from_place >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`cenv`, `env`, `raw`] >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule saved_observed_storage_read >>
  qexistsl [`cx`, `e`, `env`, `es with gas_obs := gs`, `mid`] >> simp[]
QED
