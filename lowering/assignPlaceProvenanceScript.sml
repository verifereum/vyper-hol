Theory assignPlaceProvenance
Ancestors
  loweringStateRelDefs
  assignPlaceSourceBounds assignPlacePathSeparation assignPlaceLayoutHeight
  placeMemoryLiveRegion placeMemoryTypeInterfaces bodySimAugPlaceLoad
  exprSimHypsDefs exprSimProps stmtSimDefs compileEnv words
  annassignRelayoutSource loweringPosts exprLoweringProps
  placeMemoryStateRebuild allocLimitsProps

Theorem nonbytes_expr_val_at_memory_separation:
  ~is_word_type sty /\ ~is_bytestring_type sty /\ sty <> dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  expr_val_at cenv cx sty sa sb ee v op s /\ eval_operand op s = SOME sw /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  stmt_state_rel ctx func cenv cx ee s /\ expr_sim_inv cenv cx env ee /\
  write_place cx p v ee = (INL (),ff) ==>
  type_memory_size stv = 0 \/
  w2n sw + type_memory_size stv <= w2n w \/
  w2n w + type_memory_size dtv <= w2n sw
Proof
  strip_tac >>
  `!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> metis_tac[aug_place_entry_type_agrees]) >>
  drule_all memory_place_live_region >> strip_tac >>
  drule_all nonbytes_evaluated_val_footprint >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (first_x_assum (drule_all_then strip_assume_tac) >> decide_tac)
  >- suspend "local"
QED
Resume nonbytes_expr_val_at_memory_separation[local]:
  `local_ptrs_rel func cenv ee.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  Cases_on `n = name`
  >- suspend "shared" >>
  `regions_disjoint b' sz b len` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def] >> decide_tac
QED
Resume nonbytes_expr_val_at_memory_separation[shared]:
  gvs[] >> drule_all nonbytes_nonword_local_val_path >> strip_tac >>
  Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
  rename1 `write_place cx (MemoryPlace dest path) v ee = (INL (),ff)` >>
  drule write_memory_place_entry_update >> strip_tac >>
  `local_region cenv ee.scopes s dest (w2n b'') sz'` by
    (simp[local_region_def] >> metis_tac[]) >>
  `w2n b'' + sz' <= s.vs_alloca_next /\ type_memory_size tv0 <= sz'` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `k < dimword (:256) /\ w2n b'' + k < dimword (:256)` by decide_tac >>
  `w2n (b'' + n2w k) = w2n b'' + k` by
    (`w2n (b'' + n2w k) = w2n b'' + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[] >> decide_tac) >>
  Cases_on `n = dest`
  >- suspend "same_path_root" >>
  `regions_disjoint b' sz (w2n b'') sz'` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def] >> decide_tac
QED
Resume nonbytes_expr_val_at_memory_separation[same_path_root]:
  gvs[] >>
  `b' = w2n b''` by
    (qpat_x_assum `local_region _ _ _ dest b' sz` mp_tac >>
     simp[local_region_def] >> metis_tac[]) >>
  gvs[local_path_at_def] >>
  `layout_height stv = layout_height dtv` by
    (irule (cj 1 arg_type_fits_layout_height) >>
     qexistsl_tac [`sty`, `get_tenv cx`, `dty`] >>
     gvs[vyperTypeSystemTheory.type_widens_to_def]) >>
  `stv <> dtv` by metis_tac[type_widens_to_evaluate_equal] >>
  drule_all mem_path_equal_height_windows >> strip_tac >> gvs[] >> decide_tac
QED
Finalise nonbytes_expr_val_at_memory_separation
