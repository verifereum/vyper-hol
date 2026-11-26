(* Linked posts for the single header write of a slot Pop. *)
Theory bodyPopSlotFrameMods
Ancestors
  bodyWriteTargetStageMods bodyForRangeScalarFrameMods bodyFullUnwrapRun
  exprSimPopNestedBase exprSimProps sourceUnitExecution
  vyperFiniteStoragePreservation vyperStorageTrace vyperStorageBackend
  vyperPlaceTyping vyperStorageFootprint vyperStoragePlaceRegion
  bodyPtrDefs bodyFullShadowBodyInv ptrDiscipline venomState
  loweringStateRelDefs exprLoweringProps loweringPosts

Theorem pop_slot_observed_header[local]:
  valid_horizon cx st0 H ee.storage_trace /\
  MEM (StorageRoot tr offset root) ee.storage_trace /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  (slot : bytes32) = n2w offset + n2w delta ==>
  MEM (tr,n2w offset,root) (FST H) /\
  w2n slot = w2n (n2w offset : bytes32) + delta
Proof
  simp[valid_horizon_def] >> strip_tac >>
  `MEM (tr,n2w offset,root) (FST H)` by
    (drule_all_then ACCEPT_TAC storage_observations_ok_root) >>
  `w2n (n2w offset : bytes32) + type_slot_size root <= dimword (:256)` by
    (fs[regions_consistent_def] >>
     qpat_x_assum `!b k rt. MEM (b,k,rt) (FST H) ==> _` drule >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule storage_subregion_bounds >> simp[vyperValueTheory.type_slot_size_def] >>
  strip_tac >>
  `w2n (n2w offset : bytes32) + delta < dimword (:256) /\
   delta < dimword (:256)` by decide_tac >>
  pure_rewrite_tac[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
  `(delta MOD dimword (:256)) = delta` by simp[arithmeticTheory.LESS_MOD] >>
  pop_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >>
  fs[arithmeticTheory.LESS_MOD, wordsTheory.w2n_n2w]
QED

Theorem pop_slot_clean_dead[local]:
  X SUBSET {(k,b) | storage_dead H tr st (w2n k) b} /\
  MEM (tr,root_slot,root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta ==>
  key_update X slot {} SUBSET {(k,b) | storage_dead H tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) (w2n k) b}
Proof
  strip_tac >> rw[pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD, key_update_def] >>
  irule nested_pop_storage_dead_header >>
  rpt (first_assum (irule_at Any)) >>
  fs[pred_setTheory.SUBSET_DEF, pairTheory.FORALL_PROD]
QED

Theorem pop_slot_header_taint[local]:
  stor_taint_ok_at D tn s /\
  D.d_stor = (sourceUnitExecution$cx_dead H cx).d_stor /\
  D.d_trans = (sourceUnitExecution$cx_dead H cx).d_trans /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  MEM (tr,root_slot,root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\
  u = (if tr then tstore slot (n2w (w2n (tload slot s) - 1)) s
              else sstore slot (n2w (w2n (sload slot s) - 1)) s)
      with <| vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx |> /\
  tn'.t_imm = tn.t_imm /\
  tn'.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
  tn'.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) ==>
  stor_taint_ok_at D tn' u
Proof
  strip_tac >>
  qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_at_def, sourceUnitExecutionTheory.cx_dead_def,
      sstore_def, tstore_def, sload_def, tload_def, contract_storage_def,
      contract_transient_def, combinTheory.APPLY_UPDATE_THM,
      vfmStateTheory.lookup_account_def] >>
  irule pop_slot_clean_dead >> rpt (first_assum (irule_at Any)) >> simp[]
QED

(* The non-storage clauses only mention scopes, old variables and memory. *)
Theorem pop_slot_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  stor_taint_ok_at D tn' u /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  ef.scopes = ee.scopes /\ u.vs_memory = s.vs_memory /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  tn'.t_mem = tn.t_mem ==>
  ghost_inv_at_mods D lo d cenv cx ef G' tn' u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers G' tn' p u sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, allocas_from_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem pop_slot_stmt_frame[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  MEM (tr,root_slot,root) (FST H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\
  local_ptrs_reserved cenv sa /\
  new = n2w (w2n (lookup_storage slot (get_storage cx ee tr)) - 1) /\
  ef = (set_storage cx ee tr (apply_writes slot [(0,new)] (get_storage cx ee tr)))
        with storage_trace := obs /\
  u = (if tr then tstore slot new s else sstore slot new s)
       with <| vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx |> /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx ef u
Proof
  strip_tac >>
  qabbrev_tac `q = u with vs_inst_idx := s.vs_inst_idx` >>
  `q = (if tr then tstore slot new s else sstore slot new s) with vs_vars := q.vs_vars` by
    (simp[Abbr `q`] >> qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >> simp[sstore_def,tstore_def,venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    fs[Abbr `q`, lookup_var_def] >>
  `u = q with vs_inst_idx := u.vs_inst_idx` by simp[Abbr `q`,venom_state_component_equality] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  simp[stmt_state_rel_inst_idx] >>
  irule nested_pop_updated_state_rel >>
  rpt (first_assum (irule_at Any)) >> Cases_on `tr` >> gvs[]
QED

Theorem pop_slot_write_frame_mods:
  MEM (StorageRoot tr offset root) ee.storage_trace /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  slot = n2w offset + n2w delta /\
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ee = (INL v,ef) /\
  new = n2w (w2n (lookup_storage slot (get_storage cx ee tr)) - 1) /\
  (if tr then tload slot s else sload slot s) = lookup_storage slot (get_storage cx ee tr) /\
  ef = (set_storage cx ee tr (apply_writes slot [(0,new)] (get_storage cx ee tr)))
       with storage_trace := obs /\
  u = (if tr then tstore slot new s else sstore slot new s)
       with <| vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx |> /\
  tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
  tn'.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
  tn'.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
         ee (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) aty dst G0 tn0 G tn s) ==>
  !H. valid_horizon cx st0 H ef.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ef u /\ immutable_frame_mods func cenv cx ef u /\
      storage_well_formed_on cx ef (FST H) /\ wb_frame cenv es ef sa s0 u /\
      ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (`storage_trace_frame (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))))` by
       simp[storage_trace_frame_pop_place] >>
     drule_all_then ACCEPT_TAC valid_horizon_frame) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [write_target_post_mods_def])) >>
  drule_all_then strip_assume_tac pop_slot_observed_header >>
  `ef.scopes = ee.scopes /\ ef.immutables = ee.immutables` by
    (qpat_assum `ef = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >> Cases_on `tr` >>
     simp[set_storage_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >> Cases_on `tr` >>
     simp[sstore_def,tstore_def]) >>
  rpt conj_tac
  >- (irule pop_slot_stmt_frame >> rpt (first_assum (irule_at Any)) >> simp[])
  >- (irule immutable_frame_mods_exterior_frame >> rpt (first_assum (irule_at Any)) >> simp[])
  >- (irule pop_place_preserves_storage_well_formed_on >>
      rpt (first_assum (irule_at Any)) >>
      fs[valid_horizon_def,runtime_place_typed_storage] >>
      rpt strip_tac >> gvs[] >> rpt (first_assum (irule_at Any)) >> simp[])
  >- (fs[wb_frame_def,locals_kept_def,popped_kept_def] >> rpt strip_tac >> metis_tac[])
  >- suspend "ghost" >>
  irule ghost_kept_at_clean_suffix >> first_assum (irule_at Any) >> simp[]
QED

Resume pop_slot_write_frame_mods[ghost]:
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def,loweringStateRelDefsTheory.state_rel_def,call_ctx_rel_def] >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  qpat_x_assum `dead_lo_ok_mods H _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dead_lo_ok_mods_def]) >>
  `stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_mods_def] >>
  `u = (if tr then tstore slot (n2w (w2n (tload slot s) - 1)) s
              else sstore slot (n2w (w2n (sload slot s) - 1)) s)
       with <| vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx |>` by
    (qpat_assum `u = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >> gvs[]) >>
  `stor_taint_ok_at (DF H) tn' u` by
    (drule_all_then ACCEPT_TAC pop_slot_header_taint) >>
  irule pop_slot_ghost_frame >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Finalise pop_slot_write_frame_mods
