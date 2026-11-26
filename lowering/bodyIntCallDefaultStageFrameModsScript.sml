Theory bodyIntCallDefaultStageFrameMods
Ancestors
  bodyIntCallStagePacketMods bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit
  exprLowering exprLoweringProps
  loweringStateRelDefs loweringPosts bodyMemoryDefs bodyPtrDefs
  vyperTypeEvalProofs vyperTypeInvariants vyperStorageFootprint
  vyperFiniteStoragePreservation gasOutcomeFullMods gasStorage sourceUnitExecution
  sourceLogFrames pair list alist

Theorem default_type_path_offset[local]:
  !path ty. type_path_offset (cenv_without_defaults ce tag) ty path =
            type_path_offset ce ty path
Proof
  `type_memory_bytes (cenv_without_defaults ce tag) = type_memory_bytes ce` by
    (irule compileEnvTheory.type_memory_bytes_frame >> simp[cenv_without_defaults_def]) >>
  `!ty sub. type_step_offset (cenv_without_defaults ce tag) ty sub =
            type_step_offset ce ty sub` by
    simp[oneline type_step_offset_def, cenv_without_defaults_def] >>
  Induct >> simp[type_path_offset_def]
QED

Theorem default_wb_frame[local]:
  wb_frame (cenv_without_defaults ce tag) a b sa s t = wb_frame ce a b sa s t
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, dynarray_len_untupled_def,
       local_region_def, default_type_path_offset, cenv_without_defaults_def]
QED

Theorem default_return_buf_frame[local]:
  return_buf_frame d (cenv_without_defaults ce tag) si s = return_buf_frame d ce si s
Proof
  Cases_on `d` >> simp[return_buf_frame_def, cenv_without_defaults_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def, cenv_without_defaults_def]
QED

Theorem default_ghost_inv[local]:
  ghost_inv_at_mods D lo d (cenv_without_defaults ce tag)
    (cx with stk updated_by f) st G tn s = ghost_inv_at_mods D lo d ce cx st G tn s
Proof
  Cases_on `d` >> simp[ghost_inv_at_mods_def, return_buf_ptr_def,
    bodyInvSplitTheory.imm_section_dead_mods_def, cenv_without_defaults_def] >>
  PairCases_on `x` >> simp[ghost_inv_at_mods_def, return_buf_ptr_def,
    bodyInvSplitTheory.imm_section_dead_mods_def, cenv_without_defaults_def]
QED

Theorem default_stmt_state_rel[local]:
  stmt_state_rel H ctx func (cenv_without_defaults ce tag)
    (cx with stk updated_by f) st s = stmt_state_rel H ctx func ce cx st s
Proof
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def,
       storage_vars_rel_def, transient_vars_rel_def, immutable_alloca_sep_def,
       immutable_decl_sep_alt, local_region_def, local_ptrs_rel_def,
       immutable_base_zero_def, immutables_rel_def, logs_rel_eq,
       get_module_code_stk_irrelevant, get_tenv_stk_irrelevant,
       lookup_var_slot_from_layout_context, cenv_without_defaults_def]
QED

Theorem default_immutable_frame[local]:
  immutable_frame_mods func (cenv_without_defaults ce tag)
    (cx with stk updated_by f) st s = immutable_frame_mods func ce cx st s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def,
       immutable_alloca_sep_def, immutable_decl_sep_alt, local_region_def,
       get_tenv_stk_irrelevant, cenv_without_defaults_def]
QED

Theorem default_horizon[local]:
  valid_horizon (cx with stk updated_by f) st0 H tr = valid_horizon cx st0 H tr
Proof
  simp[valid_horizon_def, storage_well_formed_on_stk, storage_observations_ok_stk]
QED

(* Transport the physical frame while retaining the caller's saved locals.
   This neither replaces the source scopes by [FEMPTY] nor re-executes an operand. *)
Theorem intcall_default_stage_frame_mods:
  (intcall_stage_ops_mods (lo,func) (cenv_without_defaults ce tag)
     (cx with stk updated_by f) sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) =
   intcall_stage_ops_mods (lo,func) ce cx sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags)) /\
  (intcall_stage_frame_mods (DF,lo,d,ctx,func) (cenv_without_defaults ce tag)
     (cx with stk updated_by f) st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin =
   intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
     (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin)
Proof
  `!sc s id b k. local_region (cenv_without_defaults ce tag) sc s id b k =
                 local_region ce sc s id b k` by simp[local_region_def, cenv_without_defaults_def] >>
  simp[intcall_stage_ops_mods_def, intcall_stage_frame_mods_def, default_wb_frame,
       ghost_kept_at_def, default_return_buf_frame, get_tenv_stk_irrelevant,
       default_horizon, default_stmt_state_rel, default_immutable_frame,
       storage_well_formed_on_stk, default_ghost_inv] >>
  Cases_on `pin` >> simp[] >> PairCases_on `x` >> simp[]
QED

Theorem intcall_default_stage_dead_lo_mods:
  dead_lo_ok_mods H (DF H) lo (cenv_without_defaults ce tag)
    (cx with stk updated_by f) = dead_lo_ok_mods H (DF H) lo ce cx
Proof
  simp[dead_lo_ok_mods_def, cx_dead_def, cenv_without_defaults_def]
QED

Theorem intcall_default_stage_outcome_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods
    (cx with stk updated_by f) st0 source (es,s,G,tn) Q R =
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods
    cx st0 source (es,s,G,tn) Q R
Proof
  simp[gas_outcome_full_mods_def, gas_bad_storage_at_def,
       storage_trace_domain_def, default_horizon]
QED
