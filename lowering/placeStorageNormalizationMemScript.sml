(* Counted normalization prefix for strict widened storage assignment. *)
Theory placeStorageNormalizationMem
Ancestors
  placeAssignContinuationMem placeStorageFixedSemantic placeStorageDynamicFrame
  placeStorageWriteProvenance exprSimHyps valueEncodingProps stmtLowering
  externalNormalizePremises compileEnv externalEntryShape exprLoweringProps
  fragExec exprSimDefs loweringPosts exprSimHypsDefs typedMemoryRankCounted
  placeMemoryCopyEffect venomState bodyMemoryDefs fragGasPathMem

Theorem storage_normalization_code_parts[local]:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    src (is_word_type dty) src_loc dty sty info bytes sa = ((),sb) ==>
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty ==>
  ?buf sm sn.
    compile_alloc_buffer bytes sa = (buf,sm) /\
    compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sn) /\
    compile_assign_value ce dst (if tr then LocTransient else LocStorage)
      buf.buf_operand F src_loc dty dty info bytes sn = ((),sb)
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[pairTheory.PAIR]
QED

Theorem place_storage_normalization_mem_mono:
  (!ctx func ce cx es st sb s t inst b sz.
    stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
    typed_copy_effect ctx func st sb s t b sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region ce es.scopes s name lb len ==>
       b+sz <= lb \/ lb+len <= b) ==>
    stmt_state_rel ctx func ce cx es t) ==>
  !ce dst loc src dty src_loc sty sa sb a func ctx cx ee env s d w p v stv ff.
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
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (loc = LocStorage \/ loc = LocTransient) /\
   type_memory_bytes ce dty < dimword (:256)) ==>
  ?sn nb bw dtv q tr mid name subs k root path delta writes.
   ci_mono sa sn /\
   loc = (if tr then LocTransient else LocStorage) /\
   compile_assign_value ce dst loc nb F src_loc dty dty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
     | _ => NONE) (type_memory_bytes ce dty) sn = ((),sb) /\
   fn_has_code sn sb func /\ local_ptrs_reserved ce sn /\
   (!x. nb = Var x ==> not_fresh_at sn x) /\
   (!x. dst = Var x ==> not_fresh_at sn x) /\
   eval_operand nb q = SOME bw /\ eval_operand dst q = SOME w /\
   evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
   well_formed_type_value dtv /\ type_memory_bytes ce dty = type_memory_size dtv /\
   val_in_memory dtv v (w2n bw) q.vs_memory /\
   w2n bw + type_memory_size dtv <= q.vs_alloca_next /\
   q.vs_alloca_next < dimword (:256) /\
   declared_storage_region cx mid name subs = SOME (tr,k,root) /\
   storage_subregion root path delta dtv /\ w2n w = w2n k + delta /\
   w2n k + type_slot_size root <= dimword (:256) /\
   (!mid' name' subs' k' root'.
      declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
      (k',root') <> (k,root) ==>
      ranges_disjoint (w2n k) (type_slot_size root)
        (w2n k') (type_slot_size root')) /\
   encode_value dtv v = SOME writes /\
   ff = set_storage cx ee tr (apply_writes w writes (get_storage cx ee tr)) /\
   stmt_state_rel ctx func ce cx ee q /\ gas_path_mem ctx func s 0 (OK q) /\
   alloca_history func q /\ return_buf_frame d ce sn q /\
   s.vs_alloca_next <= q.vs_alloca_next /\
   ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
   q.vs_inst_idx = LENGTH sn.cs_current_insts /\ q.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH q.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (!off n. q.vs_alloca_next <= off ==>
      mem_bytes_at off n q.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?tr. loc = if tr then LocTransient else LocStorage` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  drule_all normalize_return_value_layout >> strip_tac >>
  `0 < type_slot_size dtv /\ 32 <= type_memory_size dtv` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  drule_all place_storage_write_provenance >> strip_tac >>
  drule storage_normalization_code_parts >> simp[] >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn` by
    metis_tac[ci_mono_compile_alloc_buffer, cj 1 ci_mono_typed_memory_family,
              pairTheory.SND] >>
  `cs_extends sn sb` by
    metis_tac[compile_assign_value_labels, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `?sw. eval_operand src s = SOME sw` by fs[expr_val_rel_def] >>
  `~(is_bytestring_type dty /\ is_bytestring_type sty) /\
   type_memory_size dtv < dimword (:256)` by simp[] >>
  drule_all place_normalization_allocation_mem >>
  disch_then (qx_choosel_then [`u`,`bw`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?out. _` (qx_choose_then `out` strip_assume_tac) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  suspend "copy"
QED

Resume place_storage_normalization_mem_mono[copy]:
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
     metis_tac[]) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `type_memory_bytes ce sty = type_memory_size stv` by metis_tac[] >>
  mp_tac (Q.SPECL [`type_rank ce.ce_struct_fields dty`,`ce`,`get_tenv cx`,
                    `ctx`,`func`,`dty`] typed_memory_rank_forward_counted) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then drule_all >>
  disch_then (qx_choose_then `q` (map_every assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `stmt_state_rel ctx func ce cx ee q` by
    (qpat_x_assum `!ctx func ce cx es st sb s t inst b sz. _` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> disch_then assume_tac >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def] >>
     fs[regions_disjoint_def]) >>
  suspend "frames"
QED

Resume place_storage_normalization_mem_mono[frames]:
  `q.vs_alloca_next = u.vs_alloca_next /\ q.vs_labels = u.vs_labels` by
    (drule typed_copy_effect_record >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand dst q = SOME w /\ eval_operand buf.buf_operand q = SOME bw` by
    (Cases_on `dst` >> fs[eval_operand_def] >>
     metis_tac[typed_copy_effect_lookup]) >>
  `return_buf_frame d ce sn q` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >>
     simp[] >> fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `gas_path_mem ctx func s 0 (OK q)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `ci_mono sa sn` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`sn`, `buf.buf_operand`, `bw`, `q`, `tr`, `mid`, `name`,
                 `subs`, `k`, `root`, `path`, `delta`] >> simp[] >>
  suspend "projections"
QED

Resume place_storage_normalization_mem_mono[projections]:
  rpt conj_tac
  >~ [`well_formed_type_value dtv`]
  >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
  >~ [`u.vs_alloca_next < dimword (:256)`]
  >- metis_tac[alloca_room_next_lt, stmt_state_rel_def]
  >~ [`ranges_disjoint _ _ _ _`]
  >- gvs[]
  >~ [`~q.vs_halted`]
  >- metis_tac[typed_copy_effect_endpoint]
  >~ [`q.vs_current_bb = sn.cs_current_bb`]
  >- metis_tac[typed_copy_effect_endpoint]
  >~ [`q.vs_inst_idx = LENGTH sn.cs_current_insts`]
  >- metis_tac[typed_copy_effect_endpoint]
  >~ [`LENGTH s.vs_memory <= LENGTH q.vs_memory`]
  >- metis_tac[typed_copy_effect_length]
  >~ [`!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP q.vs_allocas aid = SOME entry`]
  >- metis_tac[typed_copy_effect_allocas] >>
  suspend "bytes"
QED

Resume place_storage_normalization_mem_mono[bytes]:
  markerLib.RESUME_TAC >> rpt strip_tac
  >~ [`FLOOKUP s.vs_allocas aid = SOME (off,sz)`]
  >- suspend "protected" >>
  `mem_bytes_at off n q.vs_memory = mem_bytes_at off n u.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> decide_tac) >>
  simp[]
QED

Resume place_storage_normalization_mem_mono[protected]:
  `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by
    (qpat_x_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _` irule >> simp[]) >>
  `off + sz <= w2n bw \/ w2n bw + type_memory_size dtv <= off` by
    (fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def,
        venomMemDefsTheory.regions_disjoint_def] >>
     first_x_assum (qspecl_then [`aid`, `sa.cs_next_id`] mp_tac) >>
     simp[] >> decide_tac) >>
  `mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz u.vs_memory` by
    (irule typed_copy_effect_bytes >> goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED

Finalise place_storage_normalization_mem_mono

Theorem place_storage_normalization_mem:
  (!ctx func ce cx es st sb s t inst b sz.
    stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
    typed_copy_effect ctx func st sb s t b sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region ce es.scopes s name lb len ==>
       b+sz <= lb \/ lb+len <= b) ==>
    stmt_state_rel ctx func ce cx es t) ==>
  !ce dst loc src dty src_loc sty sa sb a func ctx cx ee env s d w p v stv ff.
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
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (loc = LocStorage \/ loc = LocTransient) /\
   type_memory_bytes ce dty < dimword (:256)) ==>
  ?sn nb bw dtv q tr mid name subs k root path delta writes.
   loc = (if tr then LocTransient else LocStorage) /\
   compile_assign_value ce dst loc nb F src_loc dty dty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
     | _ => NONE) (type_memory_bytes ce dty) sn = ((),sb) /\
   fn_has_code sn sb func /\ local_ptrs_reserved ce sn /\
   (!x. nb = Var x ==> not_fresh_at sn x) /\
   (!x. dst = Var x ==> not_fresh_at sn x) /\
   eval_operand nb q = SOME bw /\ eval_operand dst q = SOME w /\
   evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
   well_formed_type_value dtv /\ type_memory_bytes ce dty = type_memory_size dtv /\
   val_in_memory dtv v (w2n bw) q.vs_memory /\
   w2n bw + type_memory_size dtv <= q.vs_alloca_next /\
   q.vs_alloca_next < dimword (:256) /\
   declared_storage_region cx mid name subs = SOME (tr,k,root) /\
   storage_subregion root path delta dtv /\ w2n w = w2n k + delta /\
   w2n k + type_slot_size root <= dimword (:256) /\
   (!mid' name' subs' k' root'.
      declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
      (k',root') <> (k,root) ==>
      ranges_disjoint (w2n k) (type_slot_size root)
        (w2n k') (type_slot_size root')) /\
   encode_value dtv v = SOME writes /\
   ff = set_storage cx ee tr (apply_writes w writes (get_storage cx ee tr)) /\
   stmt_state_rel ctx func ce cx ee q /\ gas_path_mem ctx func s 0 (OK q) /\
   alloca_history func q /\ return_buf_frame d ce sn q /\
   s.vs_alloca_next <= q.vs_alloca_next /\
   ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
   q.vs_inst_idx = LENGTH sn.cs_current_insts /\ q.vs_labels = s.vs_labels /\
   (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP q.vs_allocas aid = SOME entry) /\
   LENGTH s.vs_memory <= LENGTH q.vs_memory /\
   (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\
      (!name b len. local_region ce ee.scopes s name b len ==>
         off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s.vs_memory) /\
   (!off n. q.vs_alloca_next <= off ==>
      mem_bytes_at off n q.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_storage_normalization_mem_mono >>
  disch_then (qx_choosel_then
    [`sn`,`nb`,`bw`,`dtv`,`q`,`tr`,`mid`,`name`,`subs`,`k`,`root`,`path`,`delta`,`writes`]
    strip_assume_tac) >>
  qexistsl_tac
    [`sn`,`nb`,`bw`,`dtv`,`q`,`tr`,`mid`,`name`,`subs`,`k`,`root`,`path`,`delta`,`writes`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
