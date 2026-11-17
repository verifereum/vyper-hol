(* The joint store's ghost post, below the unbuilt statement cone. *)
Theory localMemoryStoreGhostProbe
Ancestors
  localMemoryStoreProbe robustCopyTransportPtr typedMemoryCopy
  bodyPtrDefs exprLoweringProps localPtrsProps loweringStateRelDefs
  loweringPosts compileEnv vyperState venomState valueEncoding
  valueEncodingProps valueEncodingProofs exprSimProps
  stmtSimDefs ptrDiscipline finite_map pred_set list words arithmetic

Theorem memory_subpath_ghost_post:
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  lookup_scopes id es.scopes = SOME entry /\
  lookup_scopes id ff.scopes = SOME entry' /\
  (!name. name <> id ==>
    lookup_scopes name ff.scopes = lookup_scopes name es.scopes) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME bw /\
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ value_has_type tv v /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  replace_memory_entry entry path v = INL entry' /\
  typed_copy_state_frame sa (w2n bw+k) (type_memory_size tv) s t /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n bw+k) mem) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size tv) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  lo <= w2n bw+k ==>
  ghost_inv_at D lo d cenv cx ff Gf tf t /\
  alloca_frame cenv es sa s cenv ff t /\
  (!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `local_region cenv es.scopes s id (w2n bw) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size entry.type <= cap` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `!i. ~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size tv) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
     first_x_assum irule >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n bw) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `!q. q < w2n bw+k \/ w2n bw+k+type_memory_size tv <= q ==>
    mem_bytes_at q 1 s.vs_memory = mem_bytes_at q 1 t.vs_memory` by
    (rpt strip_tac >> sym_tac >>
     qpat_x_assum `!i. _ ==> mem_bytes_at i 1 _ = _` irule >> decide_tac) >>
  `!q. (q < w2n bw+k \/ w2n bw+k+type_memory_size tv <= q) /\ q IN tf.t_mem ==>
    q IN tn.t_mem` by
    (rpt strip_tac >>
     `~(w2n bw+k <= q /\ q < w2n bw+k+type_memory_size tv)` by decide_tac >>
     metis_tac[]) >>
  drule_all robust_memory_replace_entry >> strip_tac >>
  `!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p t = SOME bw` by metis_tac[] >>
  `!name b sz. local_region cenv ff.scopes t name b sz <=>
    local_region cenv es.scopes s name b sz` by
    (rpt gen_tac >> simp[local_region_def] >>
     Cases_on `name = id` >> gvs[] >> metis_tac[]) >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "allocation_frame" >>
  rpt strip_tac >>
  `off+sz <= w2n bw \/ w2n bw+cap <= off` by metis_tac[] >>
  `~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size tv)` by decide_tac >>
  metis_tac[]
QED

Resume memory_subpath_ghost_post[allocation_frame]:
  simp[alloca_frame_def] >> rpt strip_tac
  >- (fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
      first_x_assum irule >>
      `off+sz <= w2n bw \/ w2n bw+cap <= off` by metis_tac[] >>
      decide_tac) >>
  metis_tac[]
QED

Resume memory_subpath_ghost_post[ghost]:
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "locals" >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
     first_x_assum irule >> decide_tac) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size tv)` by decide_tac >>
     metis_tac[]) >>
  `return_buf_ptr d cenv Gf tf t` by
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[ghost_inv_at_def,return_buf_ptr_def] >>
     fs[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def,stor_taint_ok_at_def,typed_copy_state_frame_def,
     venom_state_component_equality,allocas_from_def,local_ptrs_reserved_def] >>
  metis_tac[]
QED

Resume memory_subpath_ghost_post[locals]:
  rpt gen_tac >> strip_tac >>
  rename1 `lookup_scopes name ff.scopes = SOME found` >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) len)` >>
  `?old. lookup_scopes name es.scopes = SOME old` by
    (Cases_on `name = id` >> metis_tac[]) >>
  `lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
   op_taint tf (Var q) = op_taint tn (Var q)` by metis_tac[] >>
  `ptr_covers G tn q s len` by (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[ptr_covers_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `lookup_var q t = SOME nw` >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `old = found` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `local_region cenv es.scopes s name (w2n nw) len` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n bw) cap (w2n nw) len` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `type_memory_size found.type <= len /\ val_wf found.type found.value` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `!i. w2n nw <= i /\ i < w2n nw+val_footprint found.type found.value ==>
    ~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size tv)` by
    (rpt strip_tac >>
     `val_footprint found.type found.value <= type_memory_size found.type` by
       metis_tac[val_footprint_le] >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory found.type found.value (w2n nw) m` by
    (fs[ghost_inv_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  mp_tac (Q.SPECL [`tn.t_mem`,`tf.t_mem`,`s.vs_memory`,`t.vs_memory`,
    `{i | w2n (bw:bytes32)+k <= i /\ i < w2n bw+k+type_memory_size tv}`,
    `found.type`,`found.value`,`w2n (nw:bytes32)`]
    robust_val_in_memory_exterior_frame) >> simp[] >> metis_tac[]
QED

Finalise memory_subpath_ghost_post
