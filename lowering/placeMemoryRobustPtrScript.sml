(* Robust local representations after replacing a typed memory path. *)
Theory placeMemoryRobustPtr
Ancestors
  placeMemoryPathRebuild placeMemoryStateRebuild bodyPtrDefs
  robustCopyTransportPtr representationCleanPtr exprSimProps
  venomMemProofs venomState valueEncoding valueEncodingProps valueEncodingProofs
  vyperState vyperTyping list arithmetic pred_set localPtrsProps
  compileEnv loweringStateRelDefs finite_map words

Theorem memory_store_restore_witness[local]:
  !dirty dirty' mem mem' off len m.
    (!i. ~(off <= i /\ i < off+len) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN dirty' <=> i IN dirty)) /\
    mem_agree_outside dirty' mem' m ==>
    ?mix. mem_agree_outside dirty mem mix /\
      (!i. ~(off <= i /\ i < off+len) ==>
        mem_bytes_at i 1 mix = mem_bytes_at i 1 m)
Proof
  rpt strip_tac >>
  qabbrev_tac `r = (ARB:venom_state) with vs_memory := m` >>
  qabbrev_tac `mix =
    (write_memory_with_expansion off (mem_bytes_at off len mem) r).vs_memory` >>
  `mem_bytes_at off len mix = mem_bytes_at off len mem` by
    (simp[Abbr `mix`] >>
     qspecl_then [`off`, `mem_bytes_at off len mem`, `r`] mp_tac
       write_memory_mem_bytes_at_same >> simp[]) >>
  qexists_tac `mix` >> conj_tac
  >- (simp[mem_agree_outside_def] >> rpt strip_tac >>
      Cases_on `off <= i /\ i < off+len`
      >- (sym_tac >> irule mem_bytes_at_eq_byte >>
          goal_assum (drule_at Any) >> decide_tac) >>
      `i+1 <= off \/ off+len <= i` by decide_tac >>
      `mem_bytes_at i 1 mix = mem_bytes_at i 1 m` by
        simp[Abbr `mix`, Abbr `r`, write_memory_mem_bytes_at_disjoint] >>
      `mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
       (i IN dirty' <=> i IN dirty)` by
        (first_x_assum irule >> decide_tac) >>
      fs[mem_agree_outside_def] >> metis_tac[]) >>
  rpt strip_tac >> `i+1 <= off \/ off+len <= i` by decide_tac >>
  simp[Abbr `mix`, Abbr `r`, write_memory_mem_bytes_at_disjoint]
QED

Theorem typed_memory_replace_entry_robust:
  !entry entry' path k ptv v off dirty dirty' mem mem'.
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    mem_path_offset entry.type path = SOME (k,ptv) /\
    value_has_type ptv v /\ replace_memory_entry entry path v = INL entry' /\
    (!m. mem_agree_outside dirty mem m ==>
      val_in_memory entry.type entry.value off m) /\
    (!m. mem_agree_outside dirty' mem' m ==>
      val_in_memory ptv v (off+k) m) /\
    (!i. ~(off+k <= i /\ i < off+k+type_memory_size ptv) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN dirty' <=> i IN dirty)) ==>
    !m. mem_agree_outside dirty' mem' m ==>
      val_in_memory entry'.type entry'.value off m
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all memory_store_restore_witness >>
  disch_then (qx_choose_then `mix` strip_assume_tac) >>
  `val_in_memory entry.type entry.value off mix /\
   val_in_memory ptv v (off+k) m` by metis_tac[] >>
  irule typed_memory_replace_entry_frame >>
  qexistsl_tac [`entry`, `k`, `mix`, `path`, `ptv`, `v`] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule LIST_EQ >> simp[] >>
  rpt strip_tac >> rename1 `j < n` >>
  `~(off+k <= b+j /\ b+j < off+k+type_memory_size ptv)` by decide_tac >>
  `mem_bytes_at (b+j) 1 mix = mem_bytes_at (b+j) 1 m` by metis_tac[] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED


Theorem memory_place_write_locals_robust_ptr:
  !d ce cx es ff G tn s fn id path v old root cap bw k ptv tm mem'.
    ghost_inv d ce cx es G tn s /\ local_ptrs_rel fn ce es.scopes s /\
    lookup_scopes id es.scopes = SOME old /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) cap) /\
    lookup_var root s = SOME bw /\
    value_has_type old.type old.value /\ well_formed_type_value old.type /\
    mem_path_offset old.type path = SOME (k,ptv) /\ value_has_type ptv v /\
    write_place cx (MemoryPlace id path) v es = (INL (),ff) /\
    (!m. mem_agree_outside tm.t_mem mem' m ==>
      val_in_memory ptv v (w2n bw+k) m) /\
    (!i. ~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size ptv) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
    !name entry p sz.
      lookup_scopes name ff.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
      ptr_covers G tn p s sz /\
      !w m. lookup_var p s = SOME w /\ mem_agree_outside tm.t_mem mem' m ==>
        val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  drule write_memory_place_entry_update >>
  disch_then (qx_choosel_then [`before`, `after`] strip_assume_tac) >>
  `before = old` by fs[] >>
  qpat_x_assum `before = old` SUBST_ALL_TAC >>
  `local_region ce es.scopes s id (w2n bw) cap /\
   type_memory_size old.type <= cap` by
    (simp[local_region_def] >> fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `k + type_memory_size ptv <= cap` by
    (drule mem_path_offset_sound >> strip_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- suspend "root" >> suspend "other"
QED

Resume memory_place_write_locals_robust_ptr[root]:
  gvs[] >> conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule typed_memory_replace_entry_robust >>
  qexistsl_tac [`tn.t_mem`, `tm.t_mem`, `old`, `k`,
    `s.vs_memory`, `mem'`, `path`, `ptv`, `v`] >> simp[] >>
  fs[ghost_inv_def] >> metis_tac[]
QED

Resume memory_place_write_locals_robust_ptr[other]:
  `lookup_scopes name es.scopes = SOME entry` by metis_tac[] >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n bw) cap (w2n w) sz /\
   val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  `!oldmem. mem_agree_outside tn.t_mem s.vs_memory oldmem ==>
    val_in_memory entry.type entry.value (w2n w) oldmem` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `mem'`, `tn.t_mem`, `tm.t_mem`,
    `{i | w2n bw+k <= i /\ i < w2n bw+k+type_memory_size ptv}`] >>
  simp[] >> fs[regions_disjoint_def] >> decide_tac
QED

Finalise memory_place_write_locals_robust_ptr
