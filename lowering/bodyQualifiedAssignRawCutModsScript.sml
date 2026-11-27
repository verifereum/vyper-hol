(* Common operand cut for a non-mutating qualified Assign with a raw saved RHS. *)
Theory bodyQualifiedAssignRawCutMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceRawUnwrapMods
  bodyQualifiedPlaceTargetEntryMods bodySavedTargetSourceMods
  bodyFullShared bodyFullPostsMods bodyFullPredsMods
  bodyWriteTargetStageMods bodyAssignQualifiedStageJoinMods bodyAssignLocalPlaceRoutesMods
  loweringPosts loweringStateRelDefs exprLowering exprLoweringProps stmtLoweringMono compileEnv
  fragGasOriginPtr fragExec context vyperStorageFootprint venomState
  ptrDiscipline words finite_map list bodyFullMemoryFrames bodyFullShadowBodyInv
  immutableDeployAssignRanges immutableAssignRepresentation bodyPtrEnvBuiltinsLen
  aggregateEvaluatedLayout bodyCopyReadPhysicalTypeMods exprBodyPreProps
  exprReasonOperand stmtSimAugAssignPlace whitelistCheckerDecls typedMemoryCopy
  placeMemoryTypeInterfaces vyperState exprSimHypsDefs targetPlaceSim
  vyperTypeSystem vyperTypeEvalCaseProofs option

Theorem raw_cut_owned_range_floor[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  immutable_frame_mods func cenv cx ee s /\
  dead_lo_ok_mods (H : (bool # bytes32 # type_value) list # num list) D lo cenv cx /\
  allocas_from lo s /\ 0 < span /\
  ((?aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\
      b <= addr /\ addr + span <= b+n) \/
   (?id b n. local_region cenv ee.scopes s id b n /\
      b <= addr /\ addr + span <= b+n)) ==> lo <= addr
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))))))
  >- (fs[allocas_from_def] >> res_tac >> decide_tac) >>
  `0 < n` by decide_tac >>
  `immutable_decl_sep_mods cenv cx ee.scopes s.vs_vars s.vs_allocas s.vs_alloca_next` by
    fs[immutable_frame_mods_def,bodyInvSplitTheory.immutable_alloca_sep_mods_def,
       bodyInvSplitTheory.immutable_decl_sep_mods_def,immutable_alloca_sep_def] >>
  `lo <= b` by
    (irule (INST_TYPE [alpha |-> ``:256``] body_full_local_region_lower_bound_mods) >>
     rpt (first_assum (irule_at Any))) >>
  decide_tac
QED

Theorem raw_cut_bytes_placement[local]:
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME pt /\
  expr_val_at cenv cx ty sa su ee v op s /\ eval_operand op s = SOME w ==>
  0 < val_footprint pt v /\
  ((?aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\
      b <= w2n w /\ w2n w + val_footprint pt v <= b+n) \/
   (?id b n. local_region cenv ee.scopes s id b n /\
      b <= w2n w /\ w2n w + val_footprint pt v <= b+n))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_sized_type ty /\ ~is_word_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def,is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT (BytesT len))` >> Cases_on `len` >>
     fs[is_bytestring_type_def,is_word_type_def]) >>
  `32 <= val_footprint pt v` by
    (irule sized_val_footprint_header >> rpt (first_assum (irule_at Any))) >>
  conj_asm1_tac >- decide_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `pt` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem qualified_raw_cut_landing[local]:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  (!i se. MEM i (target_indices bt) /\
    expr_sim_inv_mods mods cenv cx env se ==>
      expr_body_pre_mods mods cenv cx env i se) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb
    (SOME vv) sr st shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0)
    rhs_marks v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu target_marks p ee Gz tz z /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  (!r. read_result cx r mid = (INL v,mid) ==>
    read_result cx r ee = (INL v,ee)) /\
  (!l. vv_operand vv <> Label l) /\
  (!l. FST dst <> Label l) /\
  unwrap_value cenv vv st = (op,su) /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
    not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
    not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx) /\
  return_buf_frame d cenv st z /\ return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==>
    allocas_from (w2n bw + capacity) z) /\
  (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
    ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) /\
    !rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==>
      0 < type_memory_size rt) ==>
  ?s G tn.
    qualified_assign_operand_cut_mods (DF,lo,d,gas_explicit_sites ctx shadow_ctx,
      ctx,func,PG)
      cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
      (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
    (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
      !w. eval_operand op s = SOME w ==> lo <= w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    qualified_place_raw_unwrap_owned_mods >>
  qpat_assum `!explicit PG. ?z' Gf tf. _`
    (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qexists_tac `z'` >>
  qexists_tac `Gf` >>
  qexists_tac `tf` >>
  reverse conj_tac >- suspend "floor" >>
  simp[qualified_assign_operand_cut_mods_def] >>
  qhdtm_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qpat_assum `assign_place_rhs_code_mods cenv bt e sa = _`
       (mp_then (Pos hd) strip_assume_tac qualified_assign_rhs_code_view_mods) >> gvs[]) >>
  `ci_mono sa sr` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sr st` by
    (qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono st su` by
    (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_all qualified_place_store_frame_mods >> simp[]) >>
  `return_buf_sep d cenv ee z'` by
    (`!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) z'` by
      (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK z',Gf,tf)`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
       rpt gen_tac >> disch_tac >>
       irule return_buf_allocas_suffix >>
       rpt (first_assum (irule_at Any)) >> simp[]) >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
     simp[] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  fs[ci_mono_def] >>
  conj_tac >-
   (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee z' /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  Cases_on `is_word_type (expr_type e)` >> fs[] >>
  strip_tac >> qexists_tac `sa` >> simp[]
QED

Resume qualified_raw_cut_landing[floor]:
  rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >>
  qpat_assum `qualified_assign_route_mods AssignImmCopy _ _ _ _ _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
    stmt_state_rel _ _ _ _ _ ee z' /\ _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> dead_lo_ok_mods _ _ _ _ _`
    (drule_then assume_tac) >>
  `allocas_from lo z'` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ z'`
       (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  Cases_on `is_bytestring_type (lowered_value_type cenv e)`
  >- (qpat_assum `~is_word_type (expr_type e) /\
        is_bytestring_type (lowered_value_type cenv e) ==> _`
        mp_tac >>
      (impl_tac >- simp[]) >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
      drule_all raw_cut_bytes_placement >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      irule raw_cut_owned_range_floor >>
      qpat_assum `0 < val_footprint pt v` (irule_at Any) >>
      rpt (first_assum (irule_at Any)) >>
      qexistsl [`storage_trace_horizon ee.storage_trace`,`DF (storage_trace_horizon ee.storage_trace)`] >>
      simp[]) >>
  qpat_assum `~is_word_type (expr_type e)` (fn nw =>
    qpat_assum `if is_word_type (expr_type e) then _ else _`
      (qx_choosel_then [`rt`,`w'`] (map_every assume_tac o CONJUNCTS) o
       REWRITE_RULE [nw,COND_CLAUSES])) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa su ee v op z'` by simp[] >>
  qpat_assum `!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==> _`
    (drule_then assume_tac) >>
  drule_all immutable_assign_nonbytes_source_owned >>
  simp[] >> disch_then assume_tac >>
  irule raw_cut_owned_range_floor >>
  qpat_assum `0 < type_memory_size rt` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >>
  `w' = w` by fs[] >> fs[arithmeticTheory.ADD_COMM]
  >- (disj1_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[arithmeticTheory.ADD_COMM]) >>
  disj2_tac >> qexistsl [`n`,`b`,`sz`] >> simp[arithmeticTheory.ADD_COMM]
QED
Finalise qualified_raw_cut_landing[local]

Theorem raw_cut_read_witness[local]:
  qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ marks v mid Gu tu u ==>
  ?raw. read_result cx raw mid = (INL v,mid)
Proof
  simp[qualified_assign_rhs_reached_mods_def] >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. _ = (INL v,mid with gas_obs := tail)`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL,vyperStateTheory.bind_def])) >>
  Cases_on `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
  Cases_on `q` >> simp[] >> strip_tac >>
  drule_then SUBST_ALL_TAC read_result_state >> metis_tac[]
QED

Theorem raw_cut_rhs_not_label[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sr) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) expr_body_pre_mods_inv >>
  drule_all compile_expr_reason_uniform >>
  disch_then (qspec_then `expr_type e` mp_tac) >>
  simp[reason_uniform_shape_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]
QED

Theorem raw_cut_target_not_label[local]:
  target_root bt = TopLevelNameTarget (owner,id) /\
  compile_get_target_ptr compile_expr cenv bt sr = (dst,st) ==>
  !l. FST dst <> Label l
Proof
  Cases_on `bt` >> simp[target_root_def] >> strip_tac
  >- (gvs[] >> Cases_on `FLOOKUP cenv.ce_module_vars (owner,id)` >>
      gvs[compile_get_target_ptr_def,comp_return_def] >>
      Cases_on `x` >> gvs[compile_get_target_ptr_def,comp_return_def]) >>
  irule (GEN_ALL aug_place_target_ptr_not_label) >>
  rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem raw_cut_store_split[local]:
  unwrap_value cenv vv st = (op,su) /\
  assign_place_store_code_mods cenv e (SOME vv) dst st = ((),sb) /\
  fn_has_code st sb func ==>
  fn_has_code st su func /\ fn_has_code su sb func
Proof
  strip_tac >> irule fn_has_code_split >> simp[] >>
  conj_tac
  >- (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  qpat_x_assum `assign_place_store_code_mods _ _ _ _ _ = _` mp_tac >>
  simp[assign_place_store_code_mods_def,comp_bind_def] >>
  Cases_on `FST (SND dst)` >> simp[] >>
  disch_then (assume_tac o REWRITE_RULE [pairTheory.SND] o
    AP_TERM ``SND : unit # compile_state -> compile_state``) >>
  gvs[]
  >- metis_tac[ci_mono_def,ci_mono_emit_void] >>
  metis_tac[ci_mono_def,cj 1 ci_mono_stmt_helpers]
QED

Theorem raw_cut_copy_type[local]:
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  expr_body_pre_mods mods cenv cx env e es /\
  ~is_word_type dty ==>
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) /\
  !rt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt ==>
       0 < type_memory_size rt
Proof
  strip_tac >> drule_then strip_assume_tac type_stmt_assign_base_target_value >> gvs[] >>
  `assignable_type env.type_defs (expr_type e)` by fs[type_stmt_def,AllCaseEqs()] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> rpt (first_assum (irule_at Any))) >>
  conj_asm1_tac >- metis_tac[return_source_word_widens_eq] >>
  conj_tac >- metis_tac[arg_type_fits_word_type] >>
  gen_tac >> disch_tac >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    metis_tac[assignable_type_well_formed] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    fs[well_formed_type_def,IS_SOME_EXISTS] >>
  `0 < type_memory_size tv` by
    (`type_widens_to (get_tenv cx) (expr_type e) (expr_type e)` by simp[type_widens_to_def] >>
     metis_tac[immutable_assign_widened_memory_positive]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    simp[type_widens_to_def] >>
  drule_all type_widens_to_zero_memory_size >> decide_tac
QED

Theorem raw_cut_checked_read[local]:
  contract_inv mods exps ctx cenv cx /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
    (INL p,ee with gas_obs := tail)) /\
  (?raw. read_result cx raw mid = (INL v,mid)) ==>
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  (!r. read_result cx r mid = (INL v,mid) ==> read_result cx r ee = (INL v,ee))
Proof
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qpat_assum `IS_SOME (check_contract F _ _ _)`
    (strip_assume_tac o REWRITE_RULE [IS_SOME_EXISTS]) >>
  qhdtm_assum `body_const_cells_agree_mods`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  `!r. read_result cx r mid = (INL v,mid) ==>
       read_result cx r ee = (INL v,ee) /\
       ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
         requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|>` by
    (gen_tac >> disch_tac >> irule saved_checked_target_source_update_mods >>
     qpat_assum `read_result cx r mid = _` (irule_at Any) >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl [`target_gas`,`p`] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (first_x_assum (qspec_then `raw` mp_tac) >> simp[]) >>
  gen_tac >> disch_tac >> first_x_assum (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Theorem qualified_assign_raw_cut_mods:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  (!i se. MEM i (target_indices bt) /\
    expr_sim_inv_mods mods cenv cx env se ==>
      expr_body_pre_mods mods cenv cx env i se) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb
    (SOME vv) sr st shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0)
    rhs_marks v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu target_marks p ee Gz tz z /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  fn_has_code st sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
    not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==>
    allocas_from (w2n bw + capacity) z) ==>
  ?op su s G tn.
    unwrap_value cenv vv st = (op,su) /\
    qualified_assign_operand_cut_mods (DF,lo,d,gas_explicit_sites ctx shadow_ctx,
      ctx,func,PG)
      cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
      (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) /\
    (qualified_assign_route_mods AssignImmCopy (owner,id) p (SOME vv) dty dst ==>
      !w. eval_operand op s = SOME w ==> lo <= w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    simp[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_place_store_frame_mods >>
  drule_then assume_tac raw_cut_read_witness >>
  drule_all_then (map_every assume_tac o CONJUNCTS) raw_cut_checked_read >>
  qhdtm_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qpat_assum `assign_place_rhs_code_mods cenv bt e sa = _`
       (mp_then (Pos hd) strip_assume_tac qualified_assign_rhs_code_view_mods) >> gvs[]) >>
  drule_all_then assume_tac raw_cut_rhs_not_label >>
  drule_all_then assume_tac raw_cut_target_not_label >>
  Cases_on `unwrap_value cenv vv st` >>
  rename1 `unwrap_value cenv vv st = (op,su)` >>
  drule_all_then (map_every assume_tac o CONJUNCTS) raw_cut_store_split >>
  qexistsl [`op`,`su`] >> simp[] >>
  irule qualified_raw_cut_landing >>
  qhdtm_assum `qualified_assign_rhs_reached_mods` (irule_at Any) >>
  qhdtm_assum `qualified_assign_target_reached_mods` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  conj_tac >- (qhdtm_assum `ret_pc_ok` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >> simp[]) >>
  disch_tac >> irule raw_cut_copy_type >>
  rpt (first_assum (irule_at Any)) >> fs[qualified_assign_route_mods_def]
QED
