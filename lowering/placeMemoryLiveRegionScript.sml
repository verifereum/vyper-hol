Theory placeMemoryLiveRegion
Ancestors
  loweringPosts exprSimProps exprLoweringProps compileEnv loweringStateRelDefs vyperLookup
  vyperState vyperInterpreter vyperStoragePlaceProvenance words

Theorem memory_place_live_region:
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  ?name b len. local_region cenv ee.scopes s name b len /\
    b <= w2n w /\ w2n w + type_memory_size dtv <= b + len
Proof
  Cases_on `p` >> simp[place_ptr_rel_def, slot_loc_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `?entry. lookup_scopes s' ee.scopes = SOME entry` by
    (qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
     simp[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
          lift_option_def, return_def, raise_def] >>
     Cases_on `find_containing_scope s' ee.scopes`
     >- simp[vyperStateTheory.raise_def] >>
     rename1 `find_containing_scope _ _ = SOME data` >>
     PairCases_on `data` >> simp[] >>
     metis_tac[find_containing_scope_lookup]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size tv0 <= sz` by
    (gvs[local_ptrs_rel_def] >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k) = w2n b + k` by
    (`w2n (b + n2w k) = w2n b + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[] >> decide_tac) >>
  qexistsl_tac [`s'`, `w2n b`, `sz`] >>
  conj_tac >- (simp[local_region_def] >> metis_tac[]) >> decide_tac
QED
