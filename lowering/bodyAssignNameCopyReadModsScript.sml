(* Qualify the pointers and the source update at the selected successful read. *)
Theory bodyAssignNameCopyReadMods
Ancestors
  bodyAssignNameLinkedSetup bodyCopyReadPhysicalTypeMods stmtSimAssignSource
  bodyFullPostsMods exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeSoundness vyperTypeEnvPreservation vyperScopePreservation
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeEnv vyperStatePreservation
  internalReturnMemoryInputs typedMemoryCopy bodyPtrTypeBuiltinsMemoryBounds
  exprSimWordArgs nameLoweringProps stateRelProj loweringStateRelDefs venomState
  bodyFullMemoryFrames stmtSimDeclMem exprLoweringProps exprOperandVar freshWrites words
  bodyDeclMemoryCore bodyPtrDefs vyperStorageFootprint vyperState vyperTypeArgFits
  bodyFullShadowBodyInv vyperLookup
Libs monadsyntax

Theorem selected_read_pointer[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  ~is_word_type (expr_type e) /\
  (lowered_value_type cenv e = ty \/ is_bytestring_type ty) /\
  0 < type_memory_bytes cenv ty /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
  expr_store_bound cx (post_value_type cenv e) v opr u /\
  ptr_val_ok cx (post_value_type cenv e) v opr Gi ti u /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr Gi u) ==>
  ?pt rt xs sw.
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\ value_has_type tv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
    0 < type_memory_size rt /\
    opr = Var xs /\ lookup_var xs u = SOME sw /\
    ptr_covers Gi ti xs u (type_memory_size rt) /\
    (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
    w2n sw + val_store_size rt v <= u.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) copy_read_physical_type_gas_obs_mods >>
  qpat_x_assum `?pt rt. _` (qx_choosel_then [`pt`,`rt`] (map_every assume_tac o CONJUNCTS)) >>
  `value_has_type tv v` by
    (qpat_assum `type_widens_to _ (lowered_value_type cenv e) ty`
       (mp_then Any mp_tac type_widens_to_value_has_type) >> simp[] >> metis_tac[optionTheory.SOME_11]) >>
  `expr_post H ctx func cenv cx e es sa sm s0 mid v opr u` by fs[expr_post_mods_def] >>
  `ptr_buf_ok cenv e opr Gi u` by simp[] >>
  `0 < type_memory_size rt` by
    (Cases_on `is_bytestring_type ty`
     >- (`is_bytestring_type (lowered_value_type cenv e)` by
           metis_tac[typed_copy_bytestring_source] >>
         `32 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
           simp[bytestring_memory_header_bound] >> fs[] >> decide_tac) >>
     `lowered_value_type cenv e = ty` by metis_tac[] >> gvs[]) >>
  qexistsl_tac [`pt`,`rt`] >> simp[] >>
  irule internal_return_memory_value_inputs_lowered >> simp[] >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = SOME pt`)) >> simp[]
QED

Theorem selected_read_local_type[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  FLOOKUP env.var_types id = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_scopes id mid.scopes = SOME entry ==>
  entry.type = tv /\ value_has_type tv entry.value /\ well_formed_type_value tv
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
  `entry.type = tv` by
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

Theorem selected_read_local_region[local]:
  expr_body_pre_mods mods cenv cx env e es /\ contract_inv mods exps ctx cenv cx /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v opr u /\
  ghost_inv_at_mods D lo d cenv cx mid Gi ti u /\ dead_lo_ok_mods H D lo cenv cx /\
  lookup_scopes id mid.scopes = SOME entry /\ entry.type = tv /\ 0 < type_memory_size tv /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) ==>
  ?dw. lookup_var p u = SOME dw /\ ptr_covers Gi ti p u cap /\
       local_region cenv mid.scopes u id (w2n dw) cap /\
       memory_value_rel tv entry.value (w2n dw) u.vs_memory /\
       local_backed func p u (w2n dw) cap /\ val_wf tv entry.value /\
       w2n dw + cap <= u.vs_alloca_next /\ type_memory_size tv <= cap /\
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
  `type_memory_size tv <= cap` by metis_tac[] >>
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
  qpat_assum `entry.type = tv` (fn th => pure_rewrite_tac[GSYM th]) >> simp[]
QED

Theorem assign_name_copy_read_ready_mods:
  contract_inv mods exps ctx cenv cx /\ expr_body_pre_mods mods cenv cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\ FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes cenv ty = type_memory_size tv /\
  0 < type_memory_bytes cenv ty /\ ~is_word_type (expr_type e) /\
  (lowered_value_type cenv e = ty \/ is_bytestring_type ty) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
  lower_value compile_expr cenv (expr_type e) e sa = (opr,sm) /\
  compile_assign_value cenv (Var p) LocMemory opr F loc ty
    (lowered_value_type cenv e) (type_memory_bytes cenv ty) sm = ((),sb) /\
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
  ?ff entry pt rt xs sw dw.
    (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
    ff.storage_trace = mid.storage_trace /\
    write_place cx (MemoryPlace id []) v (mid with gas_obs := []) = (INL (),ff) /\
    lookup_scopes id mid.scopes = SOME entry /\ entry.assignable /\ entry.type = tv /\
    value_has_type tv entry.value /\ well_formed_type_value tv /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\ value_has_type tv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size rt /\
    0 < type_memory_size rt /\ opr = Var xs /\ lookup_var xs u = SOME sw /\
    ptr_covers Gi ti xs u (type_memory_size rt) /\
    (!m. mem_agree_outside ti.t_mem u.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
    w2n sw + val_store_size rt v <= u.vs_alloca_next /\
    lookup_var p u = SOME dw /\ ptr_covers Gi ti p u cap /\
    local_region cenv mid.scopes u id (w2n dw) cap /\
    memory_value_rel tv entry.value (w2n dw) u.vs_memory /\
    local_backed func p u (w2n dw) cap /\ val_wf tv entry.value /\
    type_memory_size tv <= cap /\ w2n dw + cap <= u.vs_alloca_next /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
    u.vs_alloca_next < dimword (:256) /\
    local_ptrs_reserved cenv sm /\ not_fresh_at sm xs /\ not_fresh_at sm p /\
    ci_mono sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    ~block_is_terminated sb /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac assign_local_continuation_all_tails >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
     fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn eq => qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  drule_then assume_tac find_containing_scope_lookup >>
  drule_all_then (map_every assume_tac o CONJUNCTS) selected_read_local_type >>
  `dead_lo_ok_mods H0 (DF H0) lo cenv cx` by simp[] >>
  `0 < type_memory_size tv` by fs[] >>
  drule_all_then (qx_choose_then `dw` (map_every assume_tac o CONJUNCTS)) selected_read_local_region >>
  drule_all_then (qx_choosel_then [`pt`,`rt`,`xs`,`sw`] (map_every assume_tac o CONJUNCTS))
    selected_read_pointer >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sm xs` by (drule_all compile_lower_value_var >> simp[]) >>
  `not_fresh_at sm p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `~block_is_terminated sb` by (drule_all compile_assign_value_memory_widen_open >> simp[]) >>
  rename1 `find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest)` >>
  qexistsl_tac [`mid with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest`,
                `entry`,`pt`,`rt`,`xs`,`sw`,`dw`] >>
  simp[] >> simp[evaluation_state_component_equality]
QED
