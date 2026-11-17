Theory memoryPlaceStorePost
Ancestors
  assignPlaceDirectCopy placeMemoryCopyEffect placeMemoryLiveRegion
  placeMemoryStateRebuild robustCopyTransportPtr stateRelProj
  bodyPtrDefs ptrDiscipline exprLoweringProps exprSimProps exprSimHypsDefs
  loweringPosts loweringStateRelDefs vyperTypeStatePreservation placeStore
  valueEncodingProofs venomState compileEnv words list rich_list arithmetic

Theorem memory_place_replace_robust[local]:
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type entry.type entry.value /\ value_has_type ptv v /\
  replace_memory_entry entry path v = INL entry' /\
  (!m. mem_agree_outside tm mem m ==>
    val_in_memory entry.type entry.value off m) /\
  (!m. mem_agree_outside tm' mem' m ==>
    val_in_memory ptv v (off+k) m) /\
  (!q. q < off+k \/ off+k+type_memory_size ptv <= q ==>
    mem_bytes_at q 1 mem = mem_bytes_at q 1 mem') /\
  (!q. (q < off+k \/ off+k+type_memory_size ptv <= q) /\ q IN tm' ==>
    q IN tm) ==>
  (!m. mem_agree_outside tm' mem' m ==>
    val_in_memory entry'.type entry'.value off m)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qabbrev_tac `hybrid = GENLIST
    (\q. HD (mem_bytes_at q 1
      (if off+k <= q /\ q < off+k+type_memory_size ptv then mem else m)))
    (MAX (LENGTH mem) (LENGTH m))` >>
  `!q. mem_bytes_at q 1 hybrid = mem_bytes_at q 1
    (if off+k <= q /\ q < off+k+type_memory_size ptv then mem else m)` by
    (gen_tac >> irule LIST_EQ >>
     simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at, Abbr `hybrid`,
          EL_GENLIST, GSYM EL] >>
     Cases_on `off+k <= q /\ q < off+k+type_memory_size ptv` >>
     simp[] >> Cases_on `q < LENGTH mem` >>
     Cases_on `q < LENGTH m` >> simp[]) >>
  `mem_agree_outside tm mem hybrid` by
    (rw[mem_agree_outside_def] >>
     Cases_on `off+k <= i /\ i < off+k+type_memory_size ptv`
     >- simp[] >>
     `i < off+k \/ off+k+type_memory_size ptv <= i` by decide_tac >>
     `i NOTIN tm'` by metis_tac[] >>
     fs[mem_agree_outside_def] >> metis_tac[]) >>
  `val_in_memory entry.type entry.value off hybrid` by metis_tac[] >>
  irule (cj 2 placeStoreTheory.place_store_replace_memory_entry) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  qexists_tac `v` >> simp[] >> rpt strip_tac >>
  `~(off+k <= q /\ q < off+k+type_memory_size ptv)` by decide_tac >> simp[]
QED

Theorem body_assign_memory_place_store_post:
  typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv) /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  lo <= w2n dw /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory dtv v (w2n dw) mem) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  stmt_state_rel H ctx func cenv cx ff t /\
  ghost_inv_at D lo d cenv cx ff Gf tf t /\
  alloca_frame cenv ee sa s cenv ff t /\
  (!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name a len. local_region cenv ee.scopes s name a len ==>
      off+sz <= a \/ a+len <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `val_in_memory dtv v (w2n dw) t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `stmt_state_rel H ctx func cenv cx ff t /\
   alloca_frame cenv ee sa s cenv ff t` by
    (irule assign_place_copy_effect_state_frame >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "ghost" >>
  drule_all memory_place_live_region >> strip_tac >>
  rpt strip_tac >>
  `off + sz <= b \/ b + len <= off` by metis_tac[] >>
  `~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv)` by decide_tac >>
  metis_tac[]
QED

Resume body_assign_memory_place_store_post[ghost]:
  drule typed_copy_effect_record >>
  simp[venom_state_component_equality] >> strip_tac >>
  rev_drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `!x sz. not_fresh_at sa x ==>
    (ptr_covers Gf tf x t sz <=> ptr_covers G tn x s sz)` by
    (rpt strip_tac >>
     `lookup_var x t = lookup_var x s` by metis_tac[typed_copy_effect_lookup] >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def] >>
  conj_tac >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >> metis_tac[typed_copy_effect_lookup]) >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
        (irule typed_copy_effect_bytes >> metis_tac[ADD_CLAUSES]) >>
      `i IN tn.t_mem` by (first_x_assum (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  conj_tac >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Resume body_assign_memory_place_store_post[locals]:
  Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, COND_RAND, COND_RATOR] >>
  drule write_memory_place_entry_update >> strip_tac >>
  rename1 `lookup_scopes id ee.scopes = SOME entry` >>
  gvs[] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `w2n b + k < dimword (:256) /\ k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k) = w2n b + k` by
    (`w2n (b + n2w k) = w2n b + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule w2n_add_2 >> simp[] >> decide_tac) >>
  gvs[] >>
  `value_has_type entry.type entry.value` by
    (irule lookup_scopes_state_well_typed_value_has_type >>
     qexistsl_tac [`id`, `ee`] >> gvs[expr_sim_inv_def]) >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory entry'.type entry'.value (w2n b) mem` by
    (rpt strip_tac >> irule memory_place_replace_robust >>
     goal_assum (drule_at (Pat `replace_memory_entry _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tf.t_mem`] >>
     simp[ADD_COMM] >> conj_tac >- metis_tac[] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!i. _ ==> (_ <=> _)` (qspec_then `q` mp_tac) >>
       simp[] >> decide_tac) >>
     rpt strip_tac >> sym_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >> decide_tac) >>
  map_every qx_gen_tac [`name`, `other`, `xp`, `cap`] >> strip_tac >>
  `not_fresh_at sa xp` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var xp t = lookup_var xp s` by metis_tac[typed_copy_effect_lookup] >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_scopes name ee.scopes = SOME other` by metis_tac[] >>
  `ptr_covers G tn xp s cap /\
   (!w mem. lookup_var xp s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory other.type other.value (w2n w) mem)` by metis_tac[] >>
  simp[] >> rpt strip_tac >>
  fs[local_ptrs_rel_def] >>
  qpat_x_assum `!name entry p sz. _ ==> ?w. _`
    (qspecl_then [`name`, `other`, `xp`, `cap`] mp_tac) >> simp[] >> strip_tac >>
  `val_footprint other.type other.value <= cap` by
    metis_tac[exprSimPropsTheory.val_footprint_le, LESS_EQ_TRANS] >>
  `regions_disjoint (w2n w) cap (w2n b) sz` by
    (first_x_assum irule >> qexistsl_tac [`name`, `id`] >>
     simp[local_region_def]) >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tf.t_mem`,
    `{i | k + w2n b <= i /\ i < k + w2n b + type_memory_size dtv}`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      goal_assum (drule_at Any) >> decide_tac) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
Finalise body_assign_memory_place_store_post
