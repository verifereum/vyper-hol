(* The destination is already allocated when the base is read.  In
   particular unwrap may allocate again, but cannot clobber the saved pointer. *)
Theory exprSimCopiedSnapshot
Ancestors
  exprSimIfExpWidenedReattach exprSimIfExpWidenedCounted
  exprSimAggregateSource placeStoreStorage exprSimUnwrap
  exprSimCopy typedMemoryCopy valueLoadProps valueEncodingTyping
  loweringPosts exprLoweringProps exprLowering compileEnv context
  fragGasMode fragGasPath venomState venomInst finite_map list words
  localPtrsProps loweringStateRelDefs valueEncodingProps exprSimProps freshWrites
  memoryValueEncoding gasSummary fragGasSeq exprSimMemorySource venomMemDefs

Theorem copied_array_snapshot_tail:
  expr_type e = ArrayT et bd /\ post_value_type ce e = expr_type e /\
  unwrap_value ce vv sm = (src,su) /\
  compile_store_memory ce src (Var dst) (ArrayT et bd) (ArrayT et bd) su = ((),sn) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  local_ptrs_rel func ce es.scopes s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm su func /\ fn_has_code su sn func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\
  type_memory_bytes ce (ArrayT et bd) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  read_result cx raw ee = (INL v,ee) /\ value_has_type tv v /\
  not_fresh_at sm dst /\ eval_operand (Var dst) s = SOME dw /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sm.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u t. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa su s0 ee v src u /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    locals_kept ce es ee s0 t /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 t) /\
    (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es.scopes s0 name b k ==> off + len <= b \/ b + k <= off) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    lowered_value_rel (ArrayT et bd) tv v (Var dst) t /\
    gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s) [] (INL v) ee (OK t) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    typed_copy_state_frame su (w2n dw) (type_memory_size tv) u t /\
    eval_operand (Var dst) t = SOME dw /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
    (!name b len. local_region ce ee.scopes t name b len ==>
      w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_physical_framed_path >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `v` mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> gvs[]) >> strip_tac >>
  `eval_operand (Var dst) u = SOME dw` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv)` by metis_tac[] >>
  `sm.cs_next_var <= su.cs_next_var` by
    (qspecl_then [`ce`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved ce su` by
    (irule local_ptrs_reserved_next_var >> qexists `sm` >> simp[]) >>
  `!name b len. local_region ce ee.scopes u name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >> first_x_assum irule >> qexists `name` >>
     irule local_region_frame >> conj_tac
     >- (qexists `func` >> fs[vv_post_def, stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sm`, `ee.scopes`, `u`] >> simp[] >> metis_tac[]) >>
  `?sw. eval_operand src u = SOME sw /\ val_in_memory tv v (w2n sw) u.vs_memory` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [expr_post_def]) >>
     simp[expr_val_rel_def, is_word_type_def] >> metis_tac[]) >>
  `compile_copy_memory (Var dst) src (type_memory_size tv) su = ((),sn)` by
    fs[compile_store_memory_def, is_word_type_def, is_bytestring_type_def] >>
  `~u.vs_halted` by metis_tac[gas_marked_path_def, gas_path_normal] >>
  `val_wf tv v /\ val_footprint tv v <= type_memory_size tv` by
    metis_tac[value_has_type_val_wf, val_footprint_le] >>
  `type_memory_size tv < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) place_store_fixed_value_path >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (qspecl_then [`func`, `dw`, `ctx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  suspend "copy_frame"
QED

Resume copied_array_snapshot_tail[copy_frame]:
  `stmt_state_rel ctx func ce cx ee t` by
    (irule typed_copy_semantic_frame >> goal_assum (drule_at Any) >>
     fs[expr_post_def] >> metis_tac[]) >>
  `not_fresh_at su dst` by (irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `eval_operand (Var dst) t = SOME dw /\ t.vs_allocas = u.vs_allocas` by
    (fs[typed_copy_state_frame_def, venom_state_component_equality, eval_operand_def] >> metis_tac[]) >>
  `lowered_value_rel (ArrayT et bd) tv v (Var dst) t` by
    (simp[lowered_value_rel_def, is_word_type_def] >>
     metis_tac[memory_layout_bridges, memory_layout_bridge_def]) >>
  `gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s) [] (INL v) ee (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- metis_tac[read_result_gas_obs] >>
     metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at su x` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     fs[typed_copy_state_frame_def, expr_post_def] >> metis_tac[]) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s name b len` by
       (irule local_region_frame_fwd >> qexistsl [`s0`, `sa`, `es.scopes`] >>
        fs[vv_post_def]) >>
     qpat_x_assum `!name b len. local_region _ _ s _ _ _ ==> _` drule >> decide_tac) >>
  `!off len. off + len <= w2n dw \/ w2n dw + type_memory_size tv <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `locals_kept ce es ee s0 t` by
    (irule copy_buffer_locals_kept_frame >>
     qexistsl [`w2n dw`, `u`, `type_memory_size tv`] >>
     fs[expr_post_def] >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 t` by
    (strip_tac >> irule pure_frame_buffer_tail >>
     qexistsl [`w2n dw`, `type_memory_size tv`, `inst`, `u`] >>
     fs[expr_post_def, loweringStateRelDefsTheory.regions_disjoint_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory` irule >>
     decide_tac) >>
  suspend "old_allocations"
QED

Resume copied_array_snapshot_tail[old_allocations]:
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es.scopes s0 name b k ==> off + len <= b \/ b + k <= off) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (off,len)` by (fs[expr_post_def] >> metis_tac[]) >>
     `allocas_non_overlapping u` by (fs[expr_post_def, stmt_state_rel_def, state_rel_def, alloca_inv_def]) >>
     `aid <> inst.inst_id` by decide_tac >>
     `off + len <= w2n dw \/ w2n dw + type_memory_size tv <= off` by
       (qpat_x_assum `allocas_non_overlapping u`
          (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
        disch_then (qspecl_then [`aid`, `inst.inst_id`] mp_tac) >> simp[]) >>
     `mem_bytes_at off len u.vs_memory = mem_bytes_at off len s0.vs_memory` by
       (fs[expr_post_def] >>
        qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz u.vs_memory = _` irule >>
        simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory`
       (qspecl_then [`off`, `len`] mp_tac) >> simp[]) >>
  qexistsl [`u`, `t`] >> simp[] >>
  conj_tac >- (qpat_x_assum `!aid off len. _ ==> mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory` mp_tac >> simp[arithmeticTheory.ADD_COMM]) >> rpt strip_tac >>
  `local_region ce ee.scopes u name b len` by
    (irule local_region_frame >> conj_tac
     >- (qexists `func` >> fs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`su`, `ee.scopes`, `t`] >> simp[] >>
     fs[typed_copy_state_frame_def] >> metis_tac[]) >>
  res_tac >> simp[]
QED

Finalise copied_array_snapshot_tail
