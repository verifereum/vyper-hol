Theory placeMemoryContinuationMem
Ancestors
  placeStore placeMemoryStagingBoundary placeMemoryStagingLength typedMemoryRankCounted
  placeMemoryStateRebuild placeMemoryAssignForward
  placeMemoryLiveRegion placeMemoryCopyEffect stmtSimAppendStorageCompose exprSimProps
  targetPlaceSimCasesBase stmtSimAugAssignPlaceMemory
  exprLoweringProps compileEnv venomState stateFrame
  externalNormalizePremises placeAssignSourceTransport placeAssignContinuationMem
  placeMemoryTypeInterfaces valueEncodingTyping vyperTypeArgFits
  exprSimHyps bodyMemoryDefs exprSimDefs loweringPosts stmtLowering exprSimHypsDefs context
  loweringHalt abiTupleProps rich_list fragExec fragGasPathMem
Libs
  monadsyntax

Theorem memory_copy_write_place_state[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce a /\
  typed_copy_effect ctx func a b s t (w2n w) (type_memory_size tv) /\
  expr_sim_inv ce cx env es /\
  place_ptr_rel ce cx s (PlaceR p) w (SOME LocMemory) (Type ty) /\
  (!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id es.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx p v es = (INL (),ff) /\
  value_has_type tv v /\ val_in_memory tv v (w2n w) t.vs_memory ==>
  stmt_state_rel ctx func ce cx ff t
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  irule memory_place_write_stmt_state >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`a`, `s`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac
  >~ [`lookup_var x t = lookup_var x s`]
  >- metis_tac[typed_copy_effect_lookup]
  >~ [`LENGTH s.vs_memory <= LENGTH t.vs_memory`]
  >- metis_tac[typed_copy_effect_length]
  >~ [`mem_bytes_at off (type_memory_size _) _ = _`]
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      goal_assum (drule_at Any) >>
      irule immutable_local_slice_disjoint >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[stmt_state_rel_def]) >>
  fs[typed_copy_effect_def]
QED

Theorem place_memory_assign_value_mem:
  !ce dst loc src dty sty src_loc sa sb a func ctx cx ee s env v stv p w ff d.
  (compile_assign_value ce dst loc src (is_word_type dty) src_loc dty sty
     (case dty of ArrayT et (Dynamic _) =>
        SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
      | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
   (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   fn_has_code a sa func /\ fn_has_code sa sb func /\
   fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
   local_ptrs_reserved ce sa /\ ce.ce_target CapMcopy /\
   acyclic_struct_metadata ce.ce_struct_fields /\
   stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
   alloca_history func s /\ return_buf_frame d ce sa s /\
   eval_operand dst s = SOME w /\
   place_ptr_rel ce cx s (PlaceR p) w (SOME loc) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   expr_val_rel cx sty v src s /\ expr_val_at ce cx sty a sa ee v src s /\
   expr_val_own ce cx sty a sa ee v src s /\
   evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
   type_widens_to (get_tenv cx) sty dty /\
   ~is_word_type sty /\ ~is_word_type dty /\
   ~is_bytestring_type sty /\ ~is_bytestring_type dty /\ sty <> dty /\
   storage_place_region cx p /\
   (!id path entry t0. p = MemoryPlace id path /\
      lookup_scopes id ee.scopes = SOME entry /\ ce.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
   write_place cx p v ee = (INL (),ff) /\
   ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\ loc = LocMemory) ==>
  ?dtv t. evaluate_type (get_tenv cx) dty = SOME dtv /\
   gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func ce cx ff t /\
   alloca_history func t /\ return_buf_frame d ce sb t /\
   s.vs_alloca_next <= t.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH t.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (loc = LocMemory ==> val_in_memory dtv v (w2n w) t.vs_memory) /\
   (!off n. t.vs_alloca_next <= off ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) dty = SOME dtv` >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 value_has_type_val_wf] >>
  `type_memory_bytes ce sty = type_memory_size stv /\
   type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  drule_all memory_place_live_region >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `w2n w + type_memory_size dtv <= s.vs_alloca_next` by
    metis_tac[body_local_region_frontier, arithmeticTheory.LESS_EQ_TRANS] >>
  `w2n w + type_memory_size dtv < dimword (:256)` by decide_tac >>
  `0 < type_memory_size stv` by
    metis_tac[normalize_return_source_positive] >>
  drule_all normalize_source_window >> strip_tac >> gvs[] >>
  `val_in_memory stv v (w2n w') s.vs_memory` by
    gvs[expr_val_rel_def] >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  suspend "direct"
QED

Resume place_memory_assign_value_mem[staged]:
  gvs[compile_assign_value_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm)` >>
  rename1 `compile_copy_memory buf.buf_operand src (type_memory_size stv) sm = ((),sn)` >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `ci_mono sn sb` by
    metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `type_memory_size stv < dimword (:256)` by decide_tac >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[normalize_nonbytes_footprint, arithmeticTheory.LESS_EQ_REFL] >>
  drule_at (Pat `local_region _ _ _ _ _ _`) staged_source_destination_boundary_length >>
  disch_then drule >> disch_then drule >>
  simp[] >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`w`, `dtv`, `dst`] mp_tac) >>
  simp[] >>
  disch_then (qx_choosel_then [`u`, `tw`] strip_assume_tac) >>
  suspend "staged_copy"
QED

Resume place_memory_assign_value_mem[staged_copy]:
  markerLib.RESUME_TAC >>
  `ci_mono sa sm /\ ci_mono sm sn` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
  `sa.cs_next_var <= sn.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `!x. dst = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >>
     qpat_x_assum `!x. dst = Var x ==> not_fresh_at sa x` drule >>
     simp[not_fresh_at_def] >> strip_tac >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `compile_store_memory_typed ce dst dty buf.buf_operand sty sn = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sn sb u t (w2n w) (type_memory_size dtv) /\
       gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t` by
    (`!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        type_memory_bytes ce ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     irule typed_memory_rank_forward_counted >> simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     qexistsl_tac [`get_tenv cx`, `tw`, `stv`] >>
     simp[] >> fs[expr_sim_inv_def, stmt_state_rel_def] >>
     first_assum ACCEPT_TAC) >>
  suspend "staged_frame"
QED

Resume place_memory_assign_value_mem[staged_frame]:
  markerLib.RESUME_TAC >>
  `place_ptr_rel ce cx u (PlaceR p) w (SOME LocMemory) (Type dty)` by
    (irule place_ptr_rel_vars_frame >> goal_assum (drule_at Any) >>
     simp[]) >>
  `local_ptrs_reserved ce sn` by
    (fs[local_ptrs_reserved_def, not_fresh_at_def, ci_mono_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `stmt_state_rel ctx func ce cx ff t` by
    (irule memory_copy_write_place_state >>
     qpat_assum `typed_copy_effect _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >> simp[] >>
     metis_tac[memory_copy_write_place_state]) >>
  suspend "staged_posts"
QED

Resume place_memory_assign_value_mem[staged_posts]:
  markerLib.RESUME_TAC >>
  `t.vs_alloca_next = u.vs_alloca_next /\ t.vs_labels = u.vs_labels` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `t.vs_labels = s.vs_labels` by
    (`gas_path ctx func s 0 (OK u)` by
       metis_tac[cj 1 gas_path_mem_exec] >>
     drule aug_place_path_labels >> simp[]) >>
  `sn.cs_next_var <= sb.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `u`, `sn`] >>
     simp[] >> rpt strip_tac >>
     drule_all typed_copy_effect_lookup >> simp[]) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `!off n. t.vs_alloca_next <= off ==>
     mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory` by
    (rpt strip_tac >>
     `mem_bytes_at off n t.vs_memory = mem_bytes_at off n u.vs_memory` by
       (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> decide_tac) >>
     simp[] >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory = _` irule >>
     decide_tac) >>
  qexists_tac `t` >> simp[] >>
  suspend "staged_projections"
QED

Resume place_memory_assign_value_mem[staged_projections]:
  markerLib.RESUME_TAC >>
  rpt conj_tac >> rpt strip_tac
  >~ [`lookup_var x t = lookup_var x s`]
  >- (`not_fresh_at sn x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      drule_all typed_copy_effect_lookup >> simp[]) >>
  fs[typed_copy_effect_def] >>
  rpt strip_tac
  >~ [`lookup_var x t = lookup_var x s`]
  >- (`not_fresh_at sn x` by
        (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      qpat_x_assum `!x. not_fresh_at sn x ==> _` drule >> simp[]) >>
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by
    (qpat_x_assum `!aid p. FLOOKUP s.vs_allocas aid = SOME p ==> _` irule >> simp[]) >>
  `off + sz <= w2n tw \/ w2n tw + type_memory_size stv <= off` by
    (`alloca_inv u` by metis_tac[stmt_state_rel_def] >>
     fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.regions_disjoint_def] >>
     first_x_assum (qspecl_then [`aid`, `sa.cs_next_id`] mp_tac) >> simp[] >>
     decide_tac) >>
  `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz u.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac) >>
  simp[] >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory = _` irule >> simp[]
QED

Resume place_memory_assign_value_mem[direct]:
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[normalize_nonbytes_footprint] >>
  `w2n w' + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n w'` by
    (fs[expr_val_own_def] >>
     qpat_x_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _` drule >>
     decide_tac) >>
  `compile_store_memory_typed ce dst dty src sty sa = ((),sb)` by
    gvs[compile_assign_value_def, compile_store_memory_def] >>
  `?t. val_in_memory dtv v (w2n w) t.vs_memory /\
       typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv) /\
       gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t` by
    (`!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        type_memory_bytes ce ty = type_memory_size tv` by
       metis_tac[expr_sim_inv_memory_size] >>
     irule typed_memory_rank_forward_counted >>
     simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     qexistsl_tac [`get_tenv cx`, `w'`, `stv`] >>
     simp[] >> fs[expr_sim_inv_def, stmt_state_rel_def] >> metis_tac[]) >>
  suspend "direct_frame"
QED

Resume place_memory_assign_value_mem[direct_frame]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel ctx func ce cx ff t` by
    (irule memory_copy_write_place_state >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_stmt_helpers,
              ci_mono_def, pairTheory.SND] >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     simp[] >> rpt strip_tac >>
     drule_all typed_copy_effect_lookup >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  rpt conj_tac >> rpt strip_tac
  >~ [`mem_bytes_at off sz t.vs_memory = _`]
  >- (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
      decide_tac) >>
  fs[typed_copy_effect_def] >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
  decide_tac
QED

Finalise place_memory_assign_value_mem
