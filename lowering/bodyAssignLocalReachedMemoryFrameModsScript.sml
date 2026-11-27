(* Recover the selected live local at the reached target, before the store. *)
Theory bodyAssignLocalReachedMemoryFrameMods
Ancestors
  bodyAssignLocalPreStoreMods bodyQualifiedPlaceRhsPostMods
  bodyAssignQualifiedStageJoinMods bodyPlaceWriteSourceMods bodyWriteTargetStageMods
  bodyFullShared bodyFullMemoryFrames stmtSimLogCompose stmtSimProps
  exprSimWordArgs wordArgsPtr exprLoweringProps stateRelProj freshWrites
  bodyFullShadowBodyInv vyperStorageFootprint vyperEvalExprPreservesScopesDom
  vyperScopePreservation vyperTypeInvariants vyperTypeArgFits vyperTypeStatePreservation vyperTypeSystem
  nameLoweringProps assignBasePtrOffset valueEncodingProps stmtLoweringMono
  exprSimProps compileEnv words arithmetic option loweringPosts venomState
  exprSimHypsDefs vyperPlaceTyping loweringStateRelDefs bodyFullTargetDefs
  bodyPtrDefs ptrDiscipline bodyAssignLocalPlaceRoutesMods bodyMemoryDefs
  bodyFullPostsMods vyperStorageTrace vyperState list
Libs monadsyntax

Theorem typed_assign_subobject_size[local]:
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  env.type_defs = get_tenv cx /\ evaluate_type (get_tenv cx) dty = SOME ptv ==>
  0 < type_memory_size ptv
Proof
  simp[type_stmt_def,atarget_accepts_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all_then assume_tac type_widens_to_assignable_type >>
  drule_all_then assume_tac assignable_type_slot_size_pos >>
  simp[type_memory_size_pos]
QED

Theorem reached_local_type[local]:
  expr_sim_inv_mods mods cenv cx env ee /\
  lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
      simp[expr_sim_inv_mods_def,env_consistent_def,env_scopes_consistent_def,
           optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      `?rt. FLOOKUP env.var_types id = SOME rt` by
        (qpat_assum `!id entry. lookup_scopes id ee.scopes = SOME entry ==> _` drule >> simp[]) >>
      `cenv.ce_var_type id = SOME rt` by simp[] >>
      `evaluate_type (get_tenv cx) rt = SOME entry.type` by
        (qpat_assum `!id ty entry. _ ==> evaluate_type _ ty = SOME entry.type`
           (qspecl_then [`id`,`rt`,`entry`] mp_tac) >> simp[]) >>
      gvs[]) >>
  `state_well_typed ee` by fs[expr_sim_inv_mods_def] >>
  conj_tac >- drule_all_then ACCEPT_TAC lookup_scopes_state_well_typed_value_has_type >>
  fs[state_well_typed_def] >> drule_all_then ACCEPT_TAC lookup_scopes_well_typed_type
QED

Theorem reached_local_geometry[local]:
  expr_sim_inv_mods mods cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee z /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  write_target_location_mods cenv cx bt ee (PlaceR (MemoryPlace id path)) (Type dty) dst Gz z /\
  lookup_scopes id ee.scopes = SOME entry ==>
  ?p cap b off ptv dw.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p z = SOME b /\
    mem_path_offset entry.type path = SOME (off,ptv) /\
    evaluate_type (get_tenv cx) dty = SOME ptv /\
    eval_operand (FST dst) z = SOME dw /\ dw = b + n2w off /\
    w2n dw = w2n b + off /\ local_region cenv ee.scopes z id (w2n b) cap /\
    local_backed func p z (w2n b) cap /\ w2n b + cap <= z.vs_alloca_next /\
    z.vs_alloca_next < dimword (:256) /\ off + type_memory_size ptv <= cap /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  PairCases_on `dst` >> simp[write_target_location_mods_def,place_ptr_rel_def] >>
  strip_tac >>
  drule_all_then strip_assume_tac reached_local_type >> gvs[] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >> gvs[eval_operand_def] >>
  drule_then (assume_tac o MATCH_MP (SPEC_ALL alloca_room_next_lt))
    stmt_state_rel_alloca_room >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `w2n b + k < dimword (:256) /\ k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k : bytes32) = w2n b + k` by
    simp[w2n_add_2,w2n_n2w,LESS_MOD] >>
  simp[local_region_def] >> rpt (first_assum (irule_at Any)) >> simp[] >> decide_tac
QED

Theorem reached_local_ptr[local]:
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  ghost_inv_at_mods D lo d cenv cx ee Gz tz z /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) dst Gz tz z /\
  (!x. FST dst = Var x ==> not_fresh_at st x) /\
  lookup_var p z = SOME b /\ eval_operand (FST dst) z = SOME (b + n2w off) /\
  w2n b + off < dimword (:256) /\ off + n <= cap ==>
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  op_taint tz (FST dst) = {} /\ op_prov Gz (FST dst) = FLOOKUP Gz p /\
  (?x. FST dst = Var x /\ not_fresh_at st x /\ ptr_covers Gz tz x z n)
Proof
  strip_tac >>
  qhdtm_assum `ghost_inv_at_mods`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  `ptr_covers Gz tz p z cap` by (first_assum (drule_all_then strip_assume_tac) >> simp[]) >>
  `op_taint tz (FST dst) = {} /\ op_prov Gz (FST dst) = FLOOKUP Gz p` by
    fs[target_ptr_ok_def] >>
  `?base size. FLOOKUP Gz p = SOME (base,size)` by fs[ptr_covers_def] >>
  Cases_on `FST dst` >> gvs[op_prov_def,eval_operand_def] >>
  irule assign_base_ptr_covers_offset_address >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem reached_rhs_compile_mono[local]:
  ci_mono sa (SND (assign_place_rhs_code_mods cenv bt e sa))
Proof
  simp[assign_place_rhs_code_mods_def] >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
  irule ci_mono_bind >> simp[ci_mono_compile_expr_sa] >> gen_tac >> BETA_TAC >>
  irule ci_mono_bind >> simp[ci_mono_comp_return] >>
  IF_CASES_TAC >> simp[ci_mono_compile_snapshot_vv,ci_mono_comp_return]
QED

Theorem reached_assign_compile_mono[local]:
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst ==> ci_mono sa sr /\ ci_mono sr st
Proof
  simp[qualified_assign_code_mods_def] >> strip_tac >>
  conj_tac
  >- (mp_tac (SPEC_ALL reached_rhs_compile_mono) >> simp[]) >>
  qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[]
QED

Theorem local_rhs_scope_domains[local]:
  bind (eval_expr cx e) (read_result cx) es = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  simp[vyperStateTheory.bind_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_then assume_tac eval_expr_preserves_scopes_dom >>
  drule_then (fn th => simp[th]) read_result_scopes
QED

(* Feed the reached target's scope invariant with its actual source run;
   the gas observations consumed by that run are not part of the invariant. *)
Theorem local_assign_reached_source[local]:
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  type_place_target env bt = SOME (Type dty) /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  eval_target_place cx bt (mid with gas_obs := obs) = (INL p,ee) ==>
  expr_sim_inv_mods mods cenv cx env ee
Proof
  strip_tac >>
  `expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee` suffices_by simp[] >>
  irule place_write_reached_source_mods >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >> simp[]
QED

Theorem local_assign_prefix_frames[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sr /\ ret_pc_ok cenv sa s0 /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  ci_mono sa sr /\ ci_mono sr st /\ u.vs_alloca_next <= z.vs_alloca_next /\
  wb_frame cenv es mid sa s0 u /\ wb_frame cenv mid ee sr u z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  ghost_kept_at lo cenv mid sr Gu tu u Gz tz /\
  return_buf_frame d cenv sr u /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
  return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) ==>
  ret_pc_ok cenv st z /\ local_ptrs_reserved cenv st /\
  return_buf_frame d cenv st z /\ return_buf_sep d cenv ee z /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  alloca_frame cenv es sa s0 cenv ee z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP z.vs_allocas aid = SOME a) /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id
Proof
  simp[ci_mono_def] >> strip_tac >>
  `wb_frame cenv es ee sa s0 z` by
    (qhdtm_assum `stmt_state_rel`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule wb_frame_trans) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
          (fn th => qpat_assum `wb_frame cenv es mid sa s0 u`
             (mp_then (Pat `wb_frame _ _ _ _ _ _`) irule th)) ghost_kept_at_wb_trans) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by simp[] >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by decide_tac >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
   (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP z.vs_allocas aid = SOME a)` by
    fs[wb_frame_def] >>
  simp[] >> conj_tac
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`sr`] >> simp[] >>
      qpat_assum `wb_frame cenv mid ee sr u z` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >> simp[]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule return_buf_sep_locals_kept) >>
      conj_tac >- (pure_once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexists_tac `sa` >> conj_tac >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule log_wb_alloca_frame) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `ee` >> first_assum ACCEPT_TAC
QED

Theorem local_assign_reached_lower_bound[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
  immutable_frame_mods func cenv cx ee z /\ dead_lo_ok_mods H D lo cenv cx /\
  local_region cenv ee.scopes z id (w2n b) cap /\
  0 < type_memory_size ptv /\ off + type_memory_size ptv <= cap /\
  w2n dw = w2n b + off ==>
  lo <= w2n dw
Proof
  strip_tac >>
  `0 < cap` by decide_tac >>
  `immutable_decl_sep_mods cenv cx ee.scopes z.vs_vars z.vs_allocas z.vs_alloca_next` by
    (fs[immutable_frame_mods_def,bodyInvSplitTheory.immutable_decl_sep_mods_def,
        bodyInvSplitTheory.immutable_alloca_sep_mods_def,immutable_alloca_sep_def] >> metis_tac[]) >>
  `lo <= w2n b` by
    (irule body_full_local_region_lower_bound_mods >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  decide_tac
QED

Theorem assign_local_reached_memory_frame_mods:
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME (Type dty) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  contract_inv mods exps ctx cenv cx /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0) ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  (?entry old. lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL old) /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) ==>
  ?entry p cap b off ptv dw.
    local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
      (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw) ee st z Gz tz
Proof
  strip_tac >> drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
  drule_then strip_assume_tac reached_assign_compile_mono >>
  qhdtm_x_assum `qualified_assign_rhs_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qhdtm_x_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `mid with gas_obs := [] = mid /\ ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn th =>
    qpat_assum `!tail. eval_target_place _ _ _ = _`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL,th]))) >>
  qpat_assum `mid with gas_obs := [] = mid` (fn th =>
    qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL,th]))) >>
  `expr_sim_inv_mods mods cenv cx env ee` by
    (irule local_assign_reached_source >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  drule_then (assume_tac o SRULE []) local_rhs_scope_domains >>
  drule_then (assume_tac o SRULE []) eval_target_place_preserves_scopes_dom >>
  qabbrev_tac `h0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 h0 ee.storage_trace` by fs[Abbr `h0`,storage_trace_domain_def] >>
  `valid_horizon cx st0 h0 mid.storage_trace` by
    (qpat_assum `eval_target_place _ _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 h0 es.storage_trace` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `h0` (drule_then assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `h0` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  drule_all_then strip_assume_tac local_assign_prefix_frames >>
  drule_all_then strip_assume_tac reached_local_geometry >>
  suspend "assemble"
QED

Resume assign_local_reached_memory_frame_mods[assemble]:
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv_mods mods cenv cx env ee` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_mods_def,env_consistent_def,env_context_consistent_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `0 < type_memory_size ptv` by drule_all_then ACCEPT_TAC typed_assign_subobject_size >>
  `dead_lo_ok_mods h0 (DF h0) lo cenv cx` by simp[] >>
  `lo <= w2n dw` by drule_all_then ACCEPT_TAC local_assign_reached_lower_bound >>
  `w2n b + off < dimword (:256)` by decide_tac >>
  `eval_operand (FST dst) z = SOME (b + n2w off)` by simp[] >>
  drule_all_then strip_assume_tac (Q.INST [`n` |-> `type_memory_size ptv`] reached_local_ptr) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`entry`,`p`,`cap`,`b`,`off`,`ptv`,`dw`] >>
  simp[local_assign_here_mods_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >> simp[]
QED
Finalise assign_local_reached_memory_frame_mods
