(* Physical input to the local write at the actual post-target cursor.
   A saved value is not an allocation produced by compile_snapshot_vv. *)
Theory bodyAssignLocalSavedMods
Ancestors
  bodyFullPostsMods immutableRegionFrameProps assignBasePtrBoundary
  bodyPtrBopHashFootprint valueCopyBytes exprOperandVar freshWrites
  placeMemoryLiveRegion assignPlacePathSeparation assignPlaceLayoutHeight
  exprSimProps placeMemoryStateRebuild exprBodyPreProps
  stmtLowering compileEnv stmtLoweringMono words typedMemoryCopy
  exprSimHypsDefs vyperTypeInvariants option loweringPosts loweringStateRelDefs
  vyperPlaceFrames vyperTypeArgFits venomMemDefs vyperStorageFootprint
  vyperState vyperInterpreter vyperAST bodyPtrDefs ptrDiscipline context
  annassignRelayoutSource placeMemoryTypeInterfaces exprLoweringProps
  arithmetic exprLowering exprSimMemorySource targetPurePostTransport

(* For a saved code pointer in deployment, the read takes its immutable
   bytes from the module carried by the value relation, not the active one. *)
Theorem assign_local_saved_ctor_source_mods:
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
   dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee G tn u /\
   immutable_frame_mods func cenv cx ee u /\ vv_holds_mods cenv cx ty raw vv ee u) /\
  read_result cx raw mid = (INL v,mid) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> ==>
  read_result cx raw ee = (INL v,ee) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
          eval_operand (vv_operand vv) u = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     !mem. mem_agree_outside tn.t_mem u.vs_memory mem ==> val_in_memory rt v (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `read_result cx raw ee = (INL v,ee)` by
    (qpat_assum `ee = _` (once_rewrite_tac o single) >>
     simp[target_saved_read_oracles]) >>
  simp[] >> strip_tac >>
  qpat_assum `cenv.ce_is_ctor /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  Cases_on `vv` >> gvs[vv_location_def,vv_operand_def] >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  strip_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  fs[immutable_frame_mods_def] >>
  `ee.immutables = ee.immutables` by simp[] >>
  drule_all qualified_immutable_ctor_frame_mods >> simp[] >> strip_tac >>
  fs[sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[w2n_n2w,LESS_MOD] >> rpt strip_tac >>
  once_rewrite_tac[ADD_COMM] >> first_x_assum irule >> simp[]
QED


Theorem saved_local_entry_type[local]:
  expr_sim_inv_mods mods cenv cx env ee /\
  lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  gvs[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def] >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by metis_tac[IS_SOME_EXISTS] >>
  metis_tac[SOME_11]
QED

Theorem saved_local_typed_separation[local]:
  ~is_word_type sty /\ ~is_bytestring_type sty /\ sty <> dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  expr_val_at cenv cx sty sa sb ee v op s /\ eval_operand op s = SOME sw /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type dty) /\
  stmt_state_rel H ctx func cenv cx ee s /\ expr_sim_inv_mods mods cenv cx env ee /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  type_memory_size stv = 0 \/
  w2n sw + type_memory_size stv <= w2n w \/
  w2n w + type_memory_size dtv <= w2n sw
Proof
  strip_tac >>
  `!j p entry ty. MemoryPlace id path = MemoryPlace j p /\
     lookup_scopes j ee.scopes = SOME entry /\ cenv.ce_var_type j = SOME ty ==>
     evaluate_type (get_tenv cx) ty = SOME entry.type` by
    (simp[] >> metis_tac[saved_local_entry_type]) >>
  drule_all memory_place_live_region >> strip_tac >>
  drule_all nonbytes_evaluated_val_footprint >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (first_x_assum (drule_all_then strip_assume_tac) >> decide_tac) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  Cases_on `n = name`
  >- suspend "within_local" >>
  `regions_disjoint b' sz b len` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume saved_local_typed_separation[within_local]:
  gvs[] >> drule_all nonbytes_nonword_local_val_path >> strip_tac >>
  gvs[place_ptr_rel_def] >>
  drule write_memory_place_entry_update >> strip_tac >>
  `local_region cenv ee.scopes s id (w2n b'') sz'` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n b'' + sz' <= s.vs_alloca_next /\ type_memory_size tv0 <= sz'` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule_then (mp_tac o MATCH_MP alloca_room_next_lt)
       stateRelProjTheory.stmt_state_rel_alloca_room >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `w2n (b'' + n2w k) = w2n b'' + k` by
    (`k < dimword (:256) /\ w2n b'' + k < dimword (:256)` by decide_tac >>
     `w2n (b'' + n2w k) = w2n b'' + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[]) >>
  Cases_on `n = id` >- suspend "same_root" >>
  `regions_disjoint b' sz (w2n b'') sz'` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> metis_tac[]) >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume saved_local_typed_separation[same_root]:
  gvs[] >>
  `b' = w2n b''` by
    (qpat_x_assum `local_region _ _ _ id b' sz` mp_tac >>
     simp[local_region_def] >> metis_tac[]) >>
  gvs[local_path_at_def] >>
  `layout_height stv = layout_height dtv` by
    (irule (cj 1 arg_type_fits_layout_height) >>
     qexistsl [`sty`, `get_tenv cx`, `dty`] >>
     gvs[vyperTypeSystemTheory.type_widens_to_def]) >>
  `stv <> dtv` by metis_tac[type_widens_to_evaluate_equal] >>
  drule_all mem_path_equal_height_windows >> strip_tac >> gvs[] >> decide_tac
QED
Finalise saved_local_typed_separation

Theorem saved_local_physical_read[local]:
  ptr_val_ok cx pty v op G tn s /\
  evaluate_type (get_tenv cx) pty = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  eval_operand op s = SOME w /\ ~is_word_type pty /\
  value_has_type stv v /\
  (pty = sty \/ is_bytestring_type pty /\ is_bytestring_type sty) ==>
  op_taint tn op = {} /\
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v (w2n w) mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> fs[ptr_val_ok_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory ptv v (w2n w) mem` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`ptv`,`w`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  metis_tac[bytestring_val_in_memory_transfer, SOME_11]
QED

Theorem assign_local_saved_ready_mods:
  ~expr_can_mutate cenv (target_to_expr bt) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\
  compile_get_target_ptr compile_expr cenv bt sm = ((dst,SOME LocMemory,SOME (ValPT dty)),sb) /\
  unwrap_value cenv vv sb = (op,sc) /\
  compile_assign_value cenv dst LocMemory op F (vv_location vv) dty
    (lowered_value_type cenv e) (type_memory_bytes cenv dty) sc = ((),sf) /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL raw,mid with gas_obs := tail)) /\ read_result cx raw mid = (INL v,mid) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := target_gas ++ tail) =
    (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx e ee sa sc u ee v op s) /\
  expr_sim_inv_mods mods cenv cx env ee /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type dty) /\
  sty = lowered_value_type cenv e /\ ~is_word_type sty /\ ~is_word_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  (post_value_type cenv e = sty \/
   is_bytestring_type (post_value_type cenv e) /\ is_bytestring_type sty) /\
  type_widens_to (get_tenv cx) sty dty /\ value_has_type stv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\ ptr_buf_ok cenv e op G s /\
  (!w. eval_operand op s = SOME w ==>
        type_memory_size stv = 0 \/ w2n w + type_memory_size stv <= s.vs_alloca_next) ==>
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
  ?sw. eval_operand op s = SOME sw /\ op_taint tn op = {} /\
    (type_memory_size stv = 0 \/
     (?x. op = Var x /\ not_fresh_at sc x /\ ptr_covers G tn x s (type_memory_size stv)) /\
      w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv v (w2n sw) mem) /\
    (if vv_location vv = SOME LocMemory then
       ?buf sd se. compile_alloc_buffer (type_memory_size stv) sc = (buf,sd) /\
         compile_copy_memory buf.buf_operand op (type_memory_size stv) sd = ((),se) /\
         compile_store_memory cenv buf.buf_operand dst dty sty se = ((),sf)
     else
       compile_store_memory cenv op dst dty sty sc = ((),sf) /\
       (~is_bytestring_type dty /\ ~(dty = sty \/ tuple_memory_layout_eq dty sty) ==>
        type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= w2n dw \/
        w2n dw + type_memory_size dtv <= w2n sw))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `sty = lowered_value_type cenv e` SUBST_ALL_TAC >>
  conj_tac >- (drule read_result_gas_obs >> simp[bind_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then assume_tac) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s /\
   expr_val_rel cx (post_value_type cenv e) v op s /\
   expr_val_at cenv cx (post_value_type cenv e) sa sc ee v op s` by
    fs[expr_post_mods_def,expr_post_def] >>
  qpat_assum `expr_val_rel _ _ _ _ _`
    (qx_choose_then `sw` strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  `~is_word_type (post_value_type cenv e)` by metis_tac[is_bytestring_word_type] >>
  drule_all saved_local_physical_read >> strip_tac >>
  qexists `sw` >> asm_rewrite_tac[] >> conj_tac
  >- suspend "coverage" >>
  Cases_on `vv_location vv = SOME LocMemory`
  >- suspend "compiler_stage" >>
  suspend "direct"
QED

Resume assign_local_saved_ready_mods[coverage]:
  Cases_on `type_memory_size stv = 0` >- simp[] >> simp[] >>
  reverse conj_tac
  >- (qpat_assum `!w. eval_operand op s = SOME w ==> type_memory_size stv = 0 \/ _`
        (drule_then strip_assume_tac) >- fs[] >>
      once_rewrite_tac[ADD_COMM] >> first_assum ACCEPT_TAC) >>
  `?x. op = Var x /\ ptr_covers G tn x s (type_memory_size stv)` by
    (irule ptr_buf_ok_read_covers >> simp[] >>
     qexistsl [`cenv`,`e`] >> simp[GSYM NOT_ZERO_LT_ZERO]) >>
  `sm.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`bt`,`cenv`,`sm`] mp_tac ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sb p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >>
     simp[] >> irule (cj 1 compiler_compile_var) >> metis_tac[]) >>
  qexists `x` >> simp[] >>
  drule compiler_unwrap_value_var >> Cases_on `vv` >> simp[vv_operand_def]
QED

Resume assign_local_saved_ready_mods[compiler_stage]:
  qpat_x_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ _ = _` mp_tac >>
  Cases_on `compile_alloc_buffer (type_memory_size stv) sc` >>
  rename1 `compile_alloc_buffer _ sc = (buf,sd)` >>
  Cases_on `compile_copy_memory buf.buf_operand op (type_memory_size stv) sd` >>
  rename1 `compile_copy_memory _ _ _ sd = (unit,se)` >> Cases_on `unit` >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

Resume assign_local_saved_ready_mods[direct]:
  qpat_x_assum `compile_assign_value _ _ LocMemory _ F _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def] >> rpt strip_tac >>
  `~is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `post_value_type cenv e = lowered_value_type cenv e` by metis_tac[] >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v op s` by fs[] >>
  `lowered_value_type cenv e <> dty` by metis_tac[] >>
  drule_all saved_local_typed_separation >>
  simp[AC ADD_ASSOC ADD_COMM]
QED
Finalise assign_local_saved_ready_mods
