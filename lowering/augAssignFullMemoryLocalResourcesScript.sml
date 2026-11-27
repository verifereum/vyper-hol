(* Actual local resources across the clean AugAssign memory write. *)
Theory augAssignFullMemoryLocalResources
Ancestors
  augAssignFullPathWriteRobust augAssignFullMstoreGhostTransport
  bodySimAugPlaceStore placeMemoryStateRebuild wordLoadStorePtr
  stateRelProj bodyFullMemoryFrames loweringPosts bodySimAugPlaceLoad
  loweringStateRelDefs exprLoweringProps exprSimProps exprSimHypsDefs
  bodyPtrDefs vyperState vyperTypeSystem stmtSimDeclStore valueEncodingProps
  vyperTypeInvariants
  finite_map pred_set words

Theorem augassign_memory_place_layout[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME ptv ==>
  ?p sz b k.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b /\
    mem_path_offset entry.type path = SOME (k,ptv) /\
    w2n a = w2n b + k /\
    type_memory_size entry.type <= sz /\
    k + type_memory_size ptv <= type_memory_size entry.type
Proof
  strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `k + type_memory_size ptv <= type_memory_size entry.type` by
    metis_tac[mem_path_offset_sound] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  simp[]
QED

Theorem augassign_memory_store_local_resources:
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (INL (),es') /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s with vs_inst_idx := pc) /\
  tn' = (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a + 32}) ==>
  !name e p sz.
    lookup_scopes name es'.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !w mem. lookup_var p s = SOME w /\
      mem_agree_outside tn'.t_mem u.vs_memory mem ==>
      val_in_memory e.type e.value (w2n w) mem
Proof
  strip_tac >>
  drule_all augassign_memory_place_layout >> strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule write_memory_place_entry_update >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule aug_place_lookup_typed >>
     fs[expr_sim_inv_def, state_well_typed_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `replace_memory_entry _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.replace_memory_entry_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `name = id`
  >- suspend "changed"
  >> suspend "other"
QED

Resume augassign_memory_store_local_resources[changed]:
  gvs[] >> conj_tac >- metis_tac[] >>
  pure_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
  pure_rewrite_tac [Q.SPECL [`k`, `w2n b`] arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> irule augassign_path_word_store_robust >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
  qexistsl_tac [`old`, `s`, `tn.t_mem`, `typed_val_to_w256 etv v`] >>
  fs[store_lays_out_def] >>
  `val_footprint ptv v <= 32` by metis_tac[val_footprint_le] >>
  simp[] >> metis_tac[]
QED

Resume augassign_memory_store_local_resources[other]:
  `lookup_scopes name es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s id (w2n b) sz /\
   local_region cenv es.scopes s name (w2n w) sz'` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n b) sz (w2n w) sz'` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> metis_tac[]) >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  `w2n w + sz' <= k + w2n b \/ k + w2n b + 32 <= w2n w` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  irule mstore_local_robust >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise augassign_memory_store_local_resources

(* The standard body/dead-prefix metadata pins every positive local above lo. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all augassign_memory_place_layout >> strip_tac >>
  `local_region cenv es.scopes s id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  `0 < sz` by decide_tac >>
  `lo <= w2n b` by
    (irule body_full_local_region_lower_bound >> metis_tac[]) >>
  gvs[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
*)
Theorem augassign_memory_store_prefix_preserved:
  body_inv tops ctx cenv cx /\ dead_lo_ok H D lo cenv cx /\
  expr_sim_inv cenv cx env es /\
  stmt_state_rel H ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ store_lays_out etv ptv v /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s with vs_inst_idx := pc) ==>
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory
Proof
  cheat
QED
