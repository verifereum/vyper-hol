Theory placeMemoryStateRebuild
Ancestors
  placeMemoryPathRebuild placeMemoryLiveRegion placeMemoryAssignForward
  localPtrsProps exprLoweringProps loweringSlice vyperLookup vyperPlaceFrames
  vyperPlaceWriteSoundness vyperState compileEnv loweringStateRelDefs stmtSimDefs
  finite_map list pair exprSimProps valueEncodingTyping loweringPosts
  vyperStoragePlaceProvenance exprSimHypsDefs vyperTypeStatePreservation words
  vyperTypeValues venomState arithmetic

Theorem write_memory_place_entry_update:
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?entry entry'.
    lookup_scopes id ee.scopes = SOME entry /\
    replace_memory_entry entry path v = INL entry' /\
    lookup_scopes id ff.scopes = SOME entry' /\
    (!n. n <> id ==> lookup_scopes n ff.scopes = lookup_scopes n ee.scopes) /\
    ff = ee with scopes := ff.scopes
Proof
  simp[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
       lift_option_def, lift_sum_def, type_check_def, assert_def,
       set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `find_containing_scope id ee.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def,
      lift_sum_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >> gvs[return_def, raise_def] >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  qexistsl_tac [`x2`, `entry'`] >>
  simp[lookup_scopes_update, lookup_scopes_update_other]
QED

Theorem replace_memory_entry_type_path_preserves_type:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME ptv /\ value_has_type ptv v /\
  replace_memory_entry entry path v = INL entry' ==>
  entry'.type = entry.type /\ value_has_type entry'.type entry'.value
Proof
  strip_tac >> gvs[replace_memory_entry_def, AllCaseEqs()] >>
  irule assign_subscripts_type_path_preserves_type >> metis_tac[]
QED

Theorem memory_place_write_local_ptrs:
  local_ptrs_rel func cenv ee.scopes r /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p r = SOME w /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (k,ptv) /\ value_has_type ptv v /\
  val_in_memory ptv v (w2n w+k) t.vs_memory /\
  t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
  (!name e q len. lookup_scopes name ff.scopes = SOME e /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) len) ==>
      lookup_var q t = lookup_var q r) /\
  (!name b len a n.
    local_region cenv ee.scopes r name b len /\ b <= a /\ a+n <= b+len /\
    (a+n <= w2n w+k \/ w2n w+k+type_memory_size ptv <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n r.vs_memory) ==>
  local_ptrs_rel func cenv ff.scopes t
Proof
  strip_tac >> drule write_memory_place_entry_update >> strip_tac >>
  gvs[] >> rename1 `replace_memory_entry entry path v = INL new_entry` >>
  `local_region cenv ee.scopes r id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_backed func p r (w2n w) sz /\
   w2n w + sz <= r.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n w) r.vs_memory` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     qpat_x_assum `!name entry p sz. _`
       (drule_all_then strip_assume_tac) >> gvs[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  drule_all replace_memory_entry_type_path_preserves_type >> strip_tac >>
  `val_in_memory new_entry.type new_entry.value (w2n w) t.vs_memory` by
    (irule typed_memory_replace_entry_frame >> simp[] >>
     qexistsl_tac [`entry`, `k`, `r.vs_memory`, `path`, `ptv`, `v`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!name b len a n. _` (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     disch_then (qspecl_then [`b`, `n`] mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  irule local_ptrs_rel_write_local >>
  qexistsl_tac [`new_entry`, `id`, `p`, `ee.scopes`, `r`, `sz`, `w`] >>
  simp[] >> suspend "lift"
QED
Resume memory_place_write_local_ptrs[lift]:
  `!n b len. n <> id /\ local_region cenv ee.scopes r n b len ==>
      regions_disjoint (w2n w) sz b len` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) sz b sz'` by metis_tac[] >>
      sym_tac >>
      qpat_x_assum `!name b len a n. _` (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      disch_then (qspecl_then [`b`, `sz'`] mp_tac) >>
      (impl_tac >- (gvs[regions_disjoint_def] >> decide_tac)) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  irule (cj 1 value_has_type_val_wf) >> gvs[]
QED
Finalise memory_place_write_local_ptrs

Theorem memory_place_write_stmt_state:
  stmt_state_rel ctx func cenv cx ee s /\
  stmt_state_rel ctx func cenv cx ee r /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
    vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
    vs_inst_idx := r.vs_inst_idx|>) = r /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    local_region cenv ee.scopes r name b len) /\
  (!name b len a n. local_region cenv ee.scopes r name b len /\ b <= a /\
    a+n <= b+len /\ (a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n r.vs_memory) /\
  LENGTH r.vs_memory <= LENGTH t.vs_memory /\
  (cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) r.vs_memory) ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >>
  Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
  rename1 `write_place cx (MemoryPlace id path) v ee = (INL (),ff)` >>
  drule write_memory_place_entry_update >> strip_tac >>
  `local_ptrs_rel func cenv ee.scopes s /\
   local_ptrs_rel func cenv ee.scopes r` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  suspend "root"
QED
Resume memory_place_write_stmt_state[root]:
  `tv0 = entry.type` by metis_tac[] >> gvs[] >>
  `value_has_type entry.type entry.value` by
    (irule lookup_scopes_state_well_typed_value_has_type >>
     qexistsl_tac [`id`, `ee`] >> gvs[expr_sim_inv_def]) >>
  `well_formed_type_value entry.type` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `local_region cenv ee.scopes s id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_region cenv ee.scopes r id (w2n b) sz` by metis_tac[] >>
  `lookup_var p r = SOME b` by
    (qpat_x_assum `local_region _ _ r id _ _` mp_tac >>
     pure_rewrite_tac[local_region_def] >> strip_tac >> gvs[]) >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_assum `local_ptrs_rel _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `w2n (b + n2w k) = w2n b + k` by
    (`w2n (b + n2w k) = w2n b + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[] >> decide_tac) >>
  gvs[] >> suspend "assemble"
QED
Resume memory_place_write_stmt_state[assemble]:
  `!name e q len. lookup_scopes name ff.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) len) ==>
    lookup_var q t = lookup_var q r` by suspend "live_vars" >>
  `t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next` by
    (qpat_assum `_ = r` mp_tac >>
     rpt (first_x_assum kall_tac) >> simp[venom_state_component_equality]) >>
  `local_ptrs_rel func cenv ff.scopes t` by
    (irule memory_place_write_local_ptrs >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `lookup_var _ r = SOME b`)) >>
     qexists_tac `sz` >> simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b' len a n. _` (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
         disch_then (qspecl_then [`a`, `n`] mp_tac) >>
         (impl_tac >- decide_tac) >> simp[]) >>
     metis_tac[ADD_COMM]) >>
  suspend "state"
QED
Resume memory_place_write_stmt_state[live_vars]:
  rpt strip_tac >>
  `?e0. lookup_scopes name ee.scopes = SOME e0` by
    (Cases_on `name = id` >> metis_tac[]) >>
  `?wb. lookup_var q s = SOME wb` by
    (qpat_assum `local_ptrs_rel _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     metis_tac[]) >>
  `local_region cenv ee.scopes s name (w2n wb) len` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_region cenv ee.scopes r name (w2n wb) len` by metis_tac[] >>
  `lookup_var q r = SOME wb` by
    (qpat_x_assum `local_region _ _ r name _ _` mp_tac >>
     pure_rewrite_tac[local_region_def] >> strip_tac >> gvs[]) >>
  `not_fresh_at sa q` by
    (qpat_x_assum `local_ptrs_reserved _ _` mp_tac >>
     simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  metis_tac[]
QED
Resume memory_place_write_stmt_state[state]:
  `!name a n. local_region cenv ff.scopes t name a n ==>
     ?name0. local_region cenv ee.scopes r name0 a n` by suspend "regions" >>
  `immutable_base_zero cenv t` by suspend "base" >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor ee t` by
    suspend "immutables" >>
  `state_rel func cenv cx ff t` by suspend "state_frame" >>
  `immutable_alloca_sep func cenv cx ff t` by
    (irule immutable_alloca_sep_fields >>
     qexistsl_tac [`r`, `ee`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[] >> conj_tac
     >- (qpat_assum `ff = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     qpat_x_assum `stmt_state_rel _ _ _ _ ee r` mp_tac >>
     simp[stmt_state_rel_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ ee r` mp_tac >>
  qpat_x_assum `_ = r` mp_tac >>
  qpat_x_assum `state_rel _ _ _ ff t` mp_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ ff t` mp_tac >>
  qpat_x_assum `immutable_base_zero cenv t` mp_tac >>
  rpt (first_x_assum kall_tac) >>
  simp[stmt_state_rel_def, venom_state_component_equality] >>
  rpt strip_tac >>
  gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.allocas_non_overlapping_def,
      venomMemDefsTheory.alloca_next_valid_def,
      alloca_room_def, pending_alloca_size_def, fmp_room_def] >>
  metis_tac[]
QED
Resume memory_place_write_stmt_state[base]:
  `immutable_base_zero cenv s /\ immutable_base_zero cenv r` by
    metis_tac[stmt_state_rel_def] >>
  `t.vs_labels = r.vs_labels` by
    (qpat_assum `_ = r` mp_tac >>
     rpt (first_x_assum kall_tac) >> simp[venom_state_component_equality]) >>
  qpat_x_assum `immutable_base_zero cenv s` mp_tac >>
  qpat_x_assum `immutable_base_zero cenv r` mp_tac >>
  simp[immutable_base_zero_alt] >> rpt strip_tac >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  Cases_on `ib` >> gvs[] >>
  rename1 `cenv.ce_imm_alloca = SOME (Var x)` >>
  `not_fresh_at sa x` by gvs[local_ptrs_reserved_def] >>
  `lookup_var x t = lookup_var x s` by metis_tac[] >>
  gvs[lookup_var_def]
QED
Resume memory_place_write_stmt_state[regions]:
  rpt strip_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[local_region_def] >> strip_tac >>
  qexists_tac `name` >> simp[local_region_def] >>
  `?e0. lookup_scopes name ee.scopes = SOME e0` by
    (Cases_on `name = id` >> metis_tac[]) >>
  qexists_tac `e0` >> simp[] >> metis_tac[]
QED
Resume memory_place_write_stmt_state[immutables]:
  irule immutables_rel_mem_agree >> qexists_tac `r` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `_ = r` mp_tac >>
      rpt (first_x_assum kall_tac) >> simp[venom_state_component_equality]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ ee r` mp_tac >>
  simp[stmt_state_rel_def, state_rel_def]
QED
Resume memory_place_write_stmt_state[state_frame]:
  irule state_rel_frame >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ ff.scopes t`)) >>
  goal_assum (drule_at (Pat `immutables_rel _ _ _ _ ee t`)) >>
  simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ ee r` mp_tac >>
  qpat_x_assum `_ = r` mp_tac >>
  rpt (first_x_assum kall_tac) >>
  simp[stmt_state_rel_def, venom_state_component_equality] >> metis_tac[]
QED
Finalise memory_place_write_stmt_state
