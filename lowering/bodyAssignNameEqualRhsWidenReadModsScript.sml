(* Resources at the successful read of a strictly widening local assignment. *)
Theory bodyAssignNameEqualRhsWidenReadMods
Ancestors
  bodyAssignNameLinkedSetup bodyCopyReadPhysicalTypeMods stmtSimAssignSource
  bodyFullPostsMods exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeSoundness vyperTypeEnvPreservation vyperScopePreservation
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeEnv vyperStatePreservation
  internalReturnMemoryInputs typedMemoryCopy bodyPtrTypeBuiltinsMemoryBounds
  exprSimWordArgs nameLoweringProps stateRelProj loweringStateRelDefs venomState
  bodyFullMemoryFrames exprLoweringProps exprOperandVar freshWrites words
  bodyDeclMemoryCore bodyPtrDefs vyperStorageFootprint vyperState vyperTypeArgFits
  bodyFullShadowBodyInv vyperLookup annassignRelayoutSource assignPlaceLayoutHeight
  placeMemoryTypeInterfaces valueTypingMemoryProps loweringPosts exprLowering compileEnv
Libs monadsyntax

(* A strictly widening source cannot be a subpath of this destination's
   root at the same layout height. *)
Theorem widen_read_root_path_impossible[local]:
  cenv.ce_var_type id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  type_widens_to (get_tenv cx) sty ty /\ sty <> ty ==>
  ~local_path_at cenv cx id k stv
Proof
  strip_tac >>
  `layout_height stv = layout_height dtv` by
    (irule (cj 1 arg_type_fits_layout_height) >>
     qexistsl_tac [`sty`,`get_tenv cx`,`ty`] >>
     fs[vyperTypeSystemTheory.type_widens_to_def]) >>
  `stv <> dtv` by metis_tac[type_widens_to_evaluate_equal] >>
  strip_tac >> fs[local_path_at_def] >>
  `t0 = ty` by metis_tac[optionTheory.SOME_11] >>
  `tv0 = dtv` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  Cases_on `path` >- gvs[mem_path_offset_def] >>
  drule mem_path_offset_layout_height >> simp[]
QED

Theorem widen_read_direct_windows[local]:
  ~is_word_type sty /\ ~is_bytestring_type sty /\ sty <> ty /\
  type_widens_to (get_tenv cx) sty ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  cenv.ce_var_type id = SOME ty /\ 0 < type_memory_size stv /\
  expr_val_at cenv cx sty sa sm mid v (Var xs) u /\
  lookup_var xs u = SOME sw /\ local_region cenv mid.scopes u id (w2n dw) cap /\
  type_memory_size dtv <= cap /\ local_ptrs_rel func cenv mid.scopes u ==>
  w2n sw + type_memory_size stv <= w2n dw \/
  w2n dw + type_memory_size dtv <= w2n sw
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac nonbytes_evaluated_val_footprint >>
  qhdtm_x_assum `expr_val_at` (drule_all_then strip_assume_tac o REWRITE_RULE [expr_val_at_def]) >>
  gvs[eval_operand_def]
  >- (first_x_assum (drule_then strip_assume_tac) >> decide_tac) >>
  rename1 `local_val_at cenv cx n _ stv v` >>
  Cases_on `n = id`
  >- (gvs[] >> drule_all_then assume_tac nonbytes_nonword_local_val_path >>
      drule_all widen_read_root_path_impossible >>
      disch_then (qspec_then `w2n sw - b` mp_tac) >> simp[]) >>
  qhdtm_x_assum `local_ptrs_rel` (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  first_x_assum (drule_all_then assume_tac) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem widen_read_scope_type[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  FLOOKUP env.var_types id = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  lookup_scopes id mid.scopes = SOME entry ==>
  entry.type = dtv /\ value_has_type dtv entry.value /\ well_formed_type_value dtv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (map_every assume_tac o CONJUNCTS) expr_body_pre_mods_runtime_typing >>
  `runtime_consistent env cx (es with gas_obs := prefix)` by
    (qpat_assum `runtime_consistent _ _ es` mp_tac >>
     pure_rewrite_tac[runtime_consistent_def,env_consistent_def,env_scopes_consistent_def,
        env_immutables_consistent_def,state_well_typed_def,evaluation_state_accfupds] >> simp[]) >>
  qpat_x_assum `runtime_consistent _ _ (es with gas_obs := prefix)`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [runtime_consistent_def]) >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `state_well_typed mid` by
    (drule_all (REWRITE_RULE [ETA_THM] typed_expr_read_success_preserves_type) >> simp[]) >>
  `entry.type = dtv` by
    (qpat_assum `bind _ _ (es with gas_obs := prefix) = (INL v,mid)` (mp_then Any mp_tac bind_split) >>
     disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (drule_all_then assume_tac eval_expr_preserves_ec >>
         drule_then assume_tac read_result_scopes >>
         `lookup_scopes id st_mid.scopes = SOME entry` by
           (qpat_assum `mid.scopes = st_mid.scopes`
              (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
         qpat_x_assum `env_consistent env cx st_mid`
           (strip_assume_tac o REWRITE_RULE [env_consistent_def,env_scopes_consistent_def]) >>
         `evaluate_type (get_tenv cx) ty = SOME entry.type` by
           (qpat_assum `!id ty entry. _ ==> evaluate_type _ _ = SOME _`
             (qspecl_then [`id`,`ty`,`entry`] mp_tac) >> simp[]) >>
         metis_tac[optionTheory.SOME_11]) >>
     qpat_x_assum `INL _ = INR _` (mp_tac) >> simp[]) >>
  simp[] >>
  `EVERY scope_well_typed mid.scopes` by fs[state_well_typed_def] >>
  drule_all scope_well_typed_lookup_scopes >> simp[]
QED

Theorem widen_read_local_region[local]:
  expr_body_pre_mods mods cenv cx env e es /\ contract_inv mods exps ctx cenv cx /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
  ghost_inv_at_mods D lo d cenv cx mid Gi ti u /\ dead_lo_ok_mods H D lo cenv cx /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.type = dtv /\ 0 < type_memory_size dtv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) ==>
  ?dw. lookup_var p u = SOME dw /\ ptr_covers Gi ti p u cap /\
       local_region cenv mid.scopes u id (w2n dw) cap /\
       memory_value_rel dtv entry.value (w2n dw) u.vs_memory /\
       local_backed func p u (w2n dw) cap /\ val_wf dtv entry.value /\
       w2n dw + cap <= u.vs_alloca_next /\ type_memory_size dtv <= cap /\
       allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
       u.vs_alloca_next < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid v opr u` by fs[expr_post_mods_def] >>
  drule_then assume_tac expr_post_state >>
  drule_then (map_every assume_tac o CONJUNCTS) stmt_state_rel_local_ptrs_alloca >>
  drule_all_then (qx_choose_then `dw` (map_every assume_tac o CONJUNCTS)) local_ptrs_rel_value >>
  `lookup_var p u = SOME dw` by fs[eval_operand_def] >>
  `local_region cenv mid.scopes u id (w2n dw) cap` by simp[local_region_def] >>
  `type_memory_size dtv <= cap` by metis_tac[] >>
  `ptr_covers Gi ti p u cap /\ allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qhdtm_assum `ghost_inv_at_mods`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     simp[] >> first_assum (drule_all_then strip_assume_tac) >> simp[]) >>
  `lo <= w2n dw` by
    (`0 < cap` by decide_tac >>
     irule body_full_local_region_lower_bound_mods >>
     goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`D`,`H`,`env`,`es`] >>
     drule_then assume_tac expr_body_pre_mods_inv >> simp[] >>
     fs[expr_post_mods_def,immutable_frame_mods_def,bodyInvSplitTheory.immutable_decl_sep_mods_def,
        bodyInvSplitTheory.immutable_alloca_sep_mods_def,exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     metis_tac[]) >>
  `u.vs_alloca_next < dimword (:256)` by
    (drule_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL alloca_room_next_lt)) stmt_state_rel_alloca_room) >>
  qexists_tac `dw` >> simp[] >>
  qpat_assum `entry.type = dtv` (fn th => pure_rewrite_tac[GSYM th]) >> simp[]
QED

(* Physical source and post type coincide in this route; only the destination
   is widened.  The robust memory fact is at the physical source width. *)
Theorem widen_read_source_pointer[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  lowered_value_type cenv e = expr_type e /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\ 0 < type_memory_size dtv /\
  expr_post H ctx func cenv cx e es sa sm s0 mid v opr u /\
  expr_store_bound cx (post_value_type cenv e) v opr u /\
  ptr_val_ok cx (post_value_type cenv e) v opr Gi ti u /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr Gi u) ==>
  ?stv xs sw.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    ~is_word_type (lowered_value_type cenv e) /\ ~is_bytestring_type (lowered_value_type cenv e) /\
    0 < type_memory_size stv /\ value_has_type stv v /\ value_has_type dtv v /\
    opr = Var xs /\ lookup_var xs u = SOME sw /\ ptr_covers Gi ti xs u (type_memory_size stv) /\
    (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory stv v (w2n sw) m) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v (Var xs) u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (expr_type e)` by
    (fs[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  `~is_bytestring_type (expr_type e)` by
    (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) copy_read_physical_type_gas_obs_mods >>
  qpat_x_assum `?pt rt. _` (qx_choosel_then [`pt`,`stv`] (map_every assume_tac o CONJUNCTS)) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    (qpat_assum `lowered_value_type _ _ = expr_type _` (pure_rewrite_tac o single o GSYM) >>
     first_assum ACCEPT_TAC) >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> rw[] >> gvs[]) >>
  `0 < type_memory_size stv` by
    (drule_all type_widens_to_zero_memory_size >> simp[] >> decide_tac) >>
  `post_value_type cenv e = lowered_value_type cenv e` by simp[post_value_type_lowered] >>
  `ptr_buf_ok cenv e opr Gi u` by simp[] >>
  `?xs sw. opr = Var xs /\ lookup_var xs u = SOME sw /\
      ptr_covers Gi ti xs u (type_memory_size stv) /\
      (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory stv v (w2n sw) m) /\
      w2n sw + val_store_size stv v <= u.vs_alloca_next` by
    (irule internal_return_memory_value_inputs_lowered >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME pt`)) >> simp[]) >>
  `val_store_size stv v = type_memory_size stv` by
    (irule val_store_size_non_bytestring >> qexistsl_tac [`get_tenv cx`,`expr_type e`] >> simp[]) >>
  `w2n sw + type_memory_size stv <= u.vs_alloca_next` by
    (qpat_assum `w2n sw + val_store_size stv v <= _` mp_tac >> simp[]) >>
  qexistsl_tac [`stv`,`xs`,`sw`] >> simp[] >> fs[expr_post_def] >>
  qpat_assum `lowered_value_type _ _ = expr_type _` (pure_rewrite_tac o single o GSYM) >>
  first_assum ACCEPT_TAC
QED

Theorem assign_name_equal_rhs_widen_read_mods:
  contract_inv mods exps ctx cenv cx /\ expr_body_pre_mods mods cenv cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\ cenv.ce_var_type id = SOME ty /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  type_memory_bytes cenv ty = type_memory_size dtv /\ 0 < type_memory_bytes cenv ty /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  lowered_value_type cenv e = expr_type e /\ expr_type e <> ty /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  compile_expr cenv (expr_type e) e sa = (vv,sv) /\
  unwrap_value cenv vv sv = (opr,sm) /\ loc = vv_location vv /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
    expr_store_bound cx (post_value_type cenv e) v opr u /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gi ti u /\
    ptr_val_ok cx (post_value_type cenv e) v opr Gi ti u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr Gi u) /\
    mid.gas_obs = [] /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  ?ff entry stv xs sw dw.
    (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
    ff.storage_trace = mid.storage_trace /\ mid.gas_obs = [] /\
    write_place cx (MemoryPlace id []) v mid = (INL (),ff) /\
    lookup_scopes id mid.scopes = SOME entry /\ entry.assignable /\ entry.type = dtv /\
    value_has_type dtv entry.value /\ well_formed_type_value dtv /\
    ~is_word_type (lowered_value_type cenv e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    opr = Var xs /\ lookup_var xs u = SOME sw /\ lookup_var p u = SOME dw /\
    ptr_covers Gi ti xs u (type_memory_size stv) /\ ptr_covers Gi ti p u cap /\
    (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory stv v (w2n sw) m) /\
    local_region cenv mid.scopes u id (w2n dw) cap /\ type_memory_size dtv <= cap /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (loc = SOME LocMemory ==>
      expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v (Var xs) u /\
      ?b len. b <= w2n dw /\ w2n dw + type_memory_size dtv <= b + len /\
        ((?name. local_region cenv mid.scopes u name b len) \/
         ?aid. aid < sm.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,len))) /\
    (loc <> SOME LocMemory ==>
      w2n sw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
    local_ptrs_reserved cenv sm /\ not_fresh_at sm xs /\ not_fresh_at sm p /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`pre`,`sc`,`entry`,`rest`] (map_every assume_tac o CONJUNCTS))
    assign_local_continuation_all_tails >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  drule_then assume_tac find_containing_scope_lookup >>
  drule_all_then (map_every assume_tac o CONJUNCTS) widen_read_scope_type >>
  `dead_lo_ok_mods H0 (DF H0) lo cenv cx` by simp[] >>
  `0 < type_memory_size dtv` by fs[] >>
  drule_all_then (qx_choose_then `dw` (map_every assume_tac o CONJUNCTS)) widen_read_local_region >>
  `expr_post H0 ctx func cenv cx e es sa sm s0 mid v opr u` by fs[expr_post_mods_def] >>
  drule_all_then (qx_choosel_then [`stv`,`xs`,`sw`] (map_every assume_tac o CONJUNCTS))
    widen_read_source_pointer >>
  suspend "geometry"
QED

Resume assign_name_equal_rhs_widen_read_mods[geometry]:
  `local_ptrs_rel func cenv mid.scopes u` by
    (drule_then assume_tac expr_post_state >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
   lowered_value_type cenv e <> ty` by simp[] >>
  `lower_value compile_expr cenv (expr_type e) e sa = (opr,sm)` by
    simp[lower_value_def,comp_bind_def] >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm xs` by (drule_all compile_lower_value_var >> simp[]) >>
  `not_fresh_at sm p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `val_wf stv v /\ val_wf dtv v` by simp[value_has_type_memory_wf] >>
  qabbrev_tac `ff = mid with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` >>
  `ff.storage_trace = mid.storage_trace /\ ff.gas_obs = []` by simp[Abbr `ff`] >>
  `!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
    (INL (),ff with gas_obs := tail)` by simp[Abbr `ff`] >>
  `ff with gas_obs := [] = ff` by simp[evaluation_state_component_equality] >>
  `write_place cx (MemoryPlace id []) v mid = (INL (),ff)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn em =>
       qpat_assum `ff with gas_obs := [] = ff` (fn ef =>
         qpat_assum `!tail. write_place _ _ _ _ = (INL (),ff with gas_obs := tail)`
           (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [em,ef]))))) >>
  qexistsl_tac [`ff`,`entry`,`stv`,`xs`,`sw`,`dw`] >>
  simp[] >> suspend "copy_windows"
QED

Resume assign_name_equal_rhs_widen_read_mods[copy_windows]:
  conj_tac
  >- (strip_tac >> qexistsl_tac [`w2n dw`,`cap`] >> simp[] >>
      disj1_tac >> qexists_tac `id` >> first_assum ACCEPT_TAC) >>
  strip_tac >> drule_all widen_read_direct_windows >> simp[]
QED

Finalise assign_name_equal_rhs_widen_read_mods
