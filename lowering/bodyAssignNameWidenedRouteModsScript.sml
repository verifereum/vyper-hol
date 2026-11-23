(* Widening a local assignment preserves the physical return layout until the copy. *)
Theory bodyAssignNameWidenedRouteMods
Ancestors
  bodyAssignNameLinkedSetup exprSimIfExpCompat exprSimSource exprSimHypsDefs
  exprBodyPreProps compileEnv exprLowering exprLoweringProps loweringPosts typedMemoryCopy
  assignRelayoutCaller annassignRelayoutSource exprSimAggregateChildren
  exprOpenTerminals exprOpenPrimitives vyperTypeSystem vyperTypeInvariants
  vyperTypeEvalCaseProofs vyperAST words annassignRelayoutCode stmtLowering
  bodyCopyAtomicRhsTypeMods valueTypingMemoryProps vyperTypeArgFits
  exprSimProps vyperState vyperTypeExprSoundness
  stmtSimAssignSource vyperTypeEnvPreservation vyperTypeSoundness
  vyperStatePreservation vyperScopePreservation vyperLookup vyperTypeEnv
  bodyFullMemoryFrames assignRelayoutSource stateRelProj nameLoweringProps
  bodyFullShadowBodyInv bodyPtrIfExpCopyInputs exprOperandVar
  freshWrites bodyDeclMemoryCore exprSimMemDefs
  bodyFullPostsMods venomState loweringStateRelDefs bodyPtrDefs bodyInvSplit
Libs monadsyntax

Theorem widened_rhs_is_call[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?ty fid args drv. e = Call ty (IntCall fid) args drv
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all_then strip_assume_tac ifexp_lowered_type_classify >> fs[]
QED

Theorem widened_rhs_layout[local]:
  expr_body_pre_mods mods ce cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\ ~is_word_type ty /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ~is_bytestring_type ty /\ ~is_word_type (lowered_value_type ce e) /\
  ~is_bytestring_type (lowered_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) ty
Proof
  strip_tac >>
  drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  rename1 `FLOOKUP env.fn_sigs _ = SOME sg` >>
  drule_all expr_sim_inv_mods_return_type >> strip_tac >>
  fs[lowered_value_type_def, expr_type_def] >>
  `~is_word_type ty'` by metis_tac[return_source_word_widens_eq] >>
  `arg_type_fits sg.ret_ty ty'` by metis_tac[type_widens_to_def, cj 1 arg_type_fits_refl] >>
  `~is_bytestring_type ty'` by metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `~is_bytestring_type ty` by
    metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source] >>
  simp[] >> metis_tac[return_source_word_widens_eq, type_widens_from_bytestring,
                     type_widens_to_trans]
QED

Theorem widened_rhs_code[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ~is_empty_value_expr e /\ ~is_empty_value_expr (gas_shadow_expr e) /\
  (!ty sa vv sb. compile_expr ce ty e sa = (vv,sb) ==>
    (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
    ~block_is_terminated sb)
Proof
  strip_tac >> drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  simp[is_empty_value_expr_def, gasShadowTheory.gas_shadow_expr_def] >>
  rpt gen_tac >> simp[Once compile_expr_def] >> strip_tac >>
  metis_tac[internal_call_location_cases, compile_intcall_open]
QED

Theorem widened_rhs_read_layout[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  0 < type_memory_size dtv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
        type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
        0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size dtv /\
        value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v
Proof
  strip_tac >> drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  `expr_sim_inv_mods mods ce cx env (es with gas_obs := prefix)` by
    (qpat_x_assum `expr_sim_inv_mods mods ce cx env es` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_mods_def, env_consistent_def, state_well_typed_def,
                      env_scopes_consistent_def, env_immutables_consistent_def,
                      evaluation_state_accfupds] >> simp[]) >>
  drule_all (REWRITE_RULE [ETA_THM] copy_intcall_read_lowered_mods) >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  gvs[value_runtime_typed_def] >>
  drule_all assign_name_memory_bytes_mods >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all widening_zero_memory_size >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size dtv` by
    (irule assign_name_memory_bytes_mods >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
     qexistsl_tac [`env`,`es`,`mods`] >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce (Call ty' (IntCall fid) args drv)) <=
     type_memory_bytes ce ty` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     pure_rewrite_tac[type_widens_to_def] >> strip_tac
     >- gvs[] >>
     drule (cj 1 arg_type_fits_memory_bytes_mono) >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  fs[value_has_type_memory_wf] >> decide_tac
QED

Theorem widened_scope_entry[local]:
  expr_body_pre_mods mods ce cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  lookup_scopes id mid.scopes = SOME entry ==>
  entry.type = dtv /\ value_has_type dtv entry.value /\ well_formed_type_value dtv
Proof
  strip_tac >>
  drule exprBodyPreTypingPropsTheory.expr_body_pre_mods_runtime_typing >> strip_tac >>
  `runtime_consistent env cx (es with gas_obs := prefix)` by
    (qpat_x_assum `runtime_consistent _ _ _` mp_tac >>
     pure_rewrite_tac[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
          env_immutables_consistent_def, state_well_typed_def, evaluation_state_accfupds] >> simp[]) >>
  `state_well_typed mid` by suspend "typing" >>
  qpat_x_assum `runtime_consistent env cx (es with gas_obs := prefix)`
    (strip_assume_tac o REWRITE_RULE [runtime_consistent_def]) >>
  drule bind_split >> disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (drule_all eval_expr_preserves_ec >> strip_tac >> suspend "scopes") >>
  fs[]
QED

Resume widened_scope_entry[scopes]:
  drule read_result_scopes >> strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    (qpat_x_assum `env_consistent env cx st_mid`
       (strip_assume_tac o REWRITE_RULE [env_consistent_def, env_scopes_consistent_def]) >>
     metis_tac[optionTheory.SOME_11]) >>
  `EVERY scope_well_typed mid.scopes` by fs[state_well_typed_def] >>
  drule_all_then strip_assume_tac scope_well_typed_lookup_scopes >> gvs[]
QED

Resume widened_scope_entry[typing]:
  qpat_assum `runtime_consistent env cx (es with gas_obs := prefix)`
    (strip_assume_tac o REWRITE_RULE [runtime_consistent_def]) >>
  drule exprBodyPreCallSafetyPropsTheory.expr_body_pre_mods_call_evaluation_safe >> strip_tac >>
  drule_all (REWRITE_RULE [ETA_THM] typed_expr_read_success_preserves_type) >> simp[]
QED
Finalise widened_scope_entry

Theorem assign_name_widened_success_resources_mods:
  contract_inv mods exps ctx ce cx /\ expr_body_pre_mods mods ce cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\ FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) cap) /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  type_memory_bytes ce ty = type_memory_size dtv /\ 0 < type_memory_size dtv /\
  ~is_word_type ty /\ type_widens_to (get_tenv cx) (expr_type e) ty /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
     (INL v,mid with gas_obs := tail)) /\ mid.gas_obs = [] /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sB) /\
  local_ptrs_reserved ce sa /\
  expr_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func ce cx e es sa sB s0 mid v op u /\
  expr_store_bound cx (post_value_type ce e) v op u /\
  ptr_val_ok cx (post_value_type ce e) v op Gi ti u /\
  ptr_buf_ok ce e op Gi u /\
  ghost_inv_at_mods D lo d ce cx mid Gi ti u /\ dead_lo_ok_mods H D lo ce cx ==>
  ?pre sc entry rest ff stv xs sw dw.
    find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) /\
    lookup_scopes id mid.scopes = SOME entry /\ entry.assignable /\ entry.type = dtv /\
    value_has_type dtv entry.value /\ well_formed_type_value dtv /\
    ff = (mid with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) /\
    (!tail. write_place cx (MemoryPlace id []) v (mid with gas_obs := tail) =
       (INL (),ff with gas_obs := tail)) /\ ff.storage_trace = mid.storage_trace /\
    post_value_type ce e = lowered_value_type ce e /\ ~is_word_type (lowered_value_type ce e) /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) ty /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    op = Var xs /\ not_fresh_at sB xs /\ not_fresh_at sB p /\
    lookup_var xs u = SOME sw /\ lookup_var p u = SOME dw /\
    (!mem. mem_agree_outside ti.t_mem u.vs_memory mem ==> val_in_memory stv v (w2n sw) mem) /\
    ptr_covers Gi ti xs u (type_memory_size stv) /\ ptr_covers Gi ti p u cap /\
    type_memory_size dtv <= cap /\ local_region ce mid.scopes u id (w2n dw) cap /\
    w2n sw + type_memory_size stv < dimword (:256) /\ w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\ w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\ lo <= w2n dw /\
    local_ptrs_reserved ce sB /\ expr_val_at ce cx (lowered_value_type ce e) sa sB mid v (Var xs) u
Proof
  strip_tac >>
  drule_all assign_local_continuation_all_tails >>
  disch_then (qx_choosel_then [`pre`,`sc`,`entry`,`rest`] strip_assume_tac) >>
  drule_then assume_tac find_containing_scope_lookup >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     pop_assum (fn eq =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  drule_all_then strip_assume_tac widened_rhs_layout >>
  drule_all_then strip_assume_tac widened_rhs_read_layout >>
  drule_all_then strip_assume_tac widened_scope_entry >>
  qhdtm_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx mid u` by fs[expr_post_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  rename1 `eval_operand (Var p) u = SOME dw` >>
  `lookup_var p u = SOME dw` by fs[eval_operand_def] >>
  `local_region ce mid.scopes u id (w2n dw) cap` by simp[local_region_def] >>
  `val_footprint stv v = type_memory_size stv` by
    (drule_all nonbytes_evaluated_val_footprint >> simp[]) >>
  `lowered_value_type ce e <> expr_type e` by metis_tac[] >>
  `type_memory_size dtv <= cap` by metis_tac[] >>
  drule_all (Q.INST [`dlen` |-> `type_memory_size dtv`] (SPEC_ALL expr_post_live_destination_source)) >>
  disch_then (qx_choose_then `sw` (map_every assume_tac o CONJUNCTS)) >>
  suspend "coverage"
QED

Resume assign_name_widened_success_resources_mods[coverage]:
  `op_taint ti op = {} /\ ptr_mem_ok cx (lowered_value_type ce e) v op Gi ti u` by
    (qhdtm_assum `ptr_val_ok` mp_tac >>
     qpat_assum `post_value_type _ _ = _` (pure_rewrite_tac o single) >>
     simp[ptr_val_ok_def]) >>
  `?xs. op = Var xs /\ ptr_covers Gi ti xs u (type_memory_size stv)` by
    (irule ptr_buf_ok_read_covers >> simp[] >> qexistsl_tac [`ce`,`e`] >> simp[]) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs u = SOME sw` by fs[eval_operand_def] >>
  `!mem. mem_agree_outside ti.t_mem u.vs_memory mem ==> val_in_memory stv v (w2n sw) mem` by
    (qhdtm_assum `ptr_mem_ok`
       (qspecl_then [`stv`,`sw`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  `ptr_covers Gi ti p u cap /\ allocas_from lo u /\ lo <= u.vs_alloca_next` by suspend "ghost" >>
  `lo <= w2n dw` by suspend "floor" >>
  `val_store_size stv v = type_memory_size stv` by
    (drule_all val_store_size_non_bytestring >> simp[]) >>
  `w2n sw + type_memory_size stv <= u.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     simp[] >> disch_then (qspecl_then [`stv`,`sw`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sB.cs_next_var` by
    metis_tac[ci_mono_lower_value_compile_expr,ci_mono_def,pairTheory.SND] >>
  `local_ptrs_reserved ce sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sB p /\ not_fresh_at sB xs` by
    metis_tac[local_ptrs_reserved_def, compile_lower_value_var] >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sB mid v (Var xs) u` by gvs[expr_post_def] >>
  qexistsl_tac [`pre`,`sc`,`entry`,`rest`] >>
  qexists_tac `mid with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` >>
  qexistsl_tac [`stv`,`xs`,`sw`,`dw`] >> simp[] >> decide_tac
QED

Resume assign_name_widened_success_resources_mods[ghost]:
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  simp[] >> first_assum (drule_all_then strip_assume_tac) >> simp[]
QED

Resume assign_name_widened_success_resources_mods[floor]:
  `0 < cap` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `type_memory_size dtv` >> asm_rewrite_tac[]) >>
  irule (INST_TYPE [alpha |-> ``:256``] body_full_local_region_lower_bound_mods) >>
  goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `dead_lo_ok_mods _ _ _ _ _`)) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[] >>
  fs[immutable_frame_mods_def, immutable_decl_sep_mods_def,
     immutable_alloca_sep_mods_def, immutable_alloca_sep_def] >> metis_tac[]
QED
Finalise assign_name_widened_success_resources_mods
