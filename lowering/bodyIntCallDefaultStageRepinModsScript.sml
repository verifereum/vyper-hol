Theory bodyIntCallDefaultStageRepinMods
Ancestors
  bodyIntCallStagePacketMods bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts bodyPtrDefs
  sourceLogFrames pair list alist

Theorem default_repin_local_region[local]:
  local_region (ce with ce_module := src) sc s id b k =
  local_region ce sc s id b k
Proof
  simp[local_region_def]
QED

Theorem default_repin_path_offset[local]:
  !path ty. type_path_offset (ce with ce_module := src) ty path =
            type_path_offset ce ty path
Proof
  `type_memory_bytes (ce with ce_module := src) = type_memory_bytes ce` by
    (irule type_memory_bytes_frame >> simp[]) >>
  `!ty sub. type_step_offset (ce with ce_module := src) ty sub =
            type_step_offset ce ty sub` by simp[oneline type_step_offset_def] >>
  Induct >> simp[type_path_offset_def]
QED

Theorem default_repin_wb_frame[local]:
  wb_frame (ce with ce_module := src) a b sa s t = wb_frame ce a b sa s t
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, dynarray_len_untupled_def,
       default_repin_local_region, default_repin_path_offset]
QED

Theorem default_repin_return_frame[local]:
  return_buf_frame d (ce with ce_module := src) si s = return_buf_frame d ce si s
Proof
  Cases_on `d` >> simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def]
QED

Theorem default_repin_ghost_inv[local]:
  ghost_inv_at_mods D lo d (ce with ce_module := src) cx es G tn s =
  ghost_inv_at_mods D lo d ce cx es G tn s
Proof
  Cases_on `d` >> simp[ghost_inv_at_mods_def, return_buf_ptr_def,
    imm_section_dead_mods_def] >>
  PairCases_on `x` >> simp[ghost_inv_at_mods_def, return_buf_ptr_def,
    imm_section_dead_mods_def]
QED

Theorem default_repin_immutables[local]:
  immutables_rel (ce with ce_module := src) addr own ctor es s =
  immutables_rel ce addr own ctor es s
Proof
  simp[immutables_rel_def]
QED

Theorem default_repin_immutable_frame[local]:
  immutable_frame_mods func (ce with ce_module := src) cx es s =
  immutable_frame_mods func ce cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, default_repin_immutables]
QED

Theorem default_repin_immutable_at[local]:
  immutable_frame_mods func ce cx es s /\ ALOOKUP ce.ce_modules src = SOME tops ==>
  immutables_rel ce cx.txn.target src ce.ce_is_ctor es s /\
  immutable_alloca_sep func (ce with ce_module := src) cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def]
QED

Theorem default_repin_storage_vars[local]:
  (!id w. FLOOKUP ce.ce_module_vars (src,id) = SOME (StorageLoc w) ==>
    ?j. lookup_var_slot_from_layout cx F src id = SOME j /\ n2w j = w) /\
  (!id w. FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (StorageLoc w) ==>
    ?j. lookup_var_slot_from_layout cx F ce.ce_module id = SOME j /\ n2w j = w) ==>
  storage_vars_rel (ce with ce_module := src) cx = storage_vars_rel ce cx
Proof
  strip_tac >> simp[storage_vars_rel_def]
QED

Theorem default_repin_transient_vars[local]:
  (!id w. FLOOKUP ce.ce_module_vars (src,id) = SOME (TransientLoc w) ==>
    ?j. lookup_var_slot_from_layout cx T src id = SOME j /\ n2w j = w) /\
  (!id w. FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (TransientLoc w) ==>
    ?j. lookup_var_slot_from_layout cx T ce.ce_module id = SOME j /\ n2w j = w) ==>
  transient_vars_rel (ce with ce_module := src) cx = transient_vars_rel ce cx
Proof
  strip_tac >> simp[transient_vars_rel_def]
QED

Theorem default_repin_horizon_frame[local]:
  ALOOKUP ce.ce_modules src = SOME tops /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  storage_vars_rel (ce with ce_module := src) cx = storage_vars_rel ce cx /\
  transient_vars_rel (ce with ce_module := src) cx = transient_vars_rel ce cx ==>
  ((stmt_state_rel H ctx func (ce with ce_module := src) cx es s /\
    immutable_frame_mods func (ce with ce_module := src) cx es s /\ P) <=>
   (stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\ P))
Proof
  strip_tac >> simp[default_repin_immutable_frame] >>
  Cases_on `immutable_frame_mods func ce cx es s` >> simp[] >>
  `immutables_rel ce cx.txn.target src ce.ce_is_ctor es s /\
   immutable_alloca_sep func (ce with ce_module := src) cx es s` by
    (irule default_repin_immutable_at >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
   immutable_alloca_sep func ce cx es s` by
    (drule default_repin_immutable_at >>
     disch_then (qspecl_then [`caller_tops`, `ce.ce_module`] mp_tac) >> simp[]) >>
  simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       local_ptrs_rel_def, default_repin_local_region, default_repin_immutables,
       immutable_base_zero_def, sourceLogFramesTheory.logs_rel_eq]
QED

(* The proof view changes only the active module of the compiler environment.
   Both directions retain the same source/target cut and immutable frame. *)
Theorem intcall_default_stage_repin_mods:
  ALOOKUP ce.ce_modules src = SOME tops /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME caller_tops /\
  (!id w. FLOOKUP ce.ce_module_vars (src,id) = SOME (StorageLoc w) ==>
    ?j. lookup_var_slot_from_layout cx F src id = SOME j /\ n2w j = w) /\
  (!id w. FLOOKUP ce.ce_module_vars (src,id) = SOME (TransientLoc w) ==>
    ?j. lookup_var_slot_from_layout cx T src id = SOME j /\ n2w j = w) /\
  (!id w. FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (StorageLoc w) ==>
    ?j. lookup_var_slot_from_layout cx F ce.ce_module id = SOME j /\ n2w j = w) /\
  (!id w. FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (TransientLoc w) ==>
    ?j. lookup_var_slot_from_layout cx T ce.ce_module id = SOME j /\ n2w j = w) ==>
  (intcall_stage_ops_mods (lo,func) (ce with ce_module := src)
     cx sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) =
   intcall_stage_ops_mods (lo,func) ce cx sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags)) /\
  (intcall_stage_frame_mods (DF,lo,d,ctx,func) (ce with ce_module := src)
     cx st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin =
   intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
     (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin)
Proof
  strip_tac >> conj_tac
  >- simp[intcall_stage_ops_mods_def, default_repin_local_region] >>
  `storage_vars_rel (ce with ce_module := src) cx = storage_vars_rel ce cx` by
    (irule default_repin_storage_vars >> simp[]) >>
  `transient_vars_rel (ce with ce_module := src) cx = transient_vars_rel ce cx` by
    (irule default_repin_transient_vars >> simp[]) >>
  `!H. (stmt_state_rel H ctx func (ce with ce_module := src) cx esi s /\
        immutable_frame_mods func (ce with ce_module := src) cx esi s /\
        storage_well_formed_on cx esi (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx esi G tn s) <=>
       (stmt_state_rel H ctx func ce cx esi s /\ immutable_frame_mods func ce cx esi s /\
        storage_well_formed_on cx esi (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx esi G tn s)` by
    (gen_tac >> irule default_repin_horizon_frame >> metis_tac[]) >>
  simp[intcall_stage_frame_mods_def, default_repin_local_region, default_repin_wb_frame,
       ghost_kept_at_def, default_repin_return_frame, default_repin_ghost_inv]
QED

Theorem intcall_default_stage_repin_guards_mods:
  dead_lo_ok_mods H (DF H) lo (ce with ce_module := src) cx =
  dead_lo_ok_mods H (DF H) lo ce cx
Proof
  simp[dead_lo_ok_mods_def]
QED
