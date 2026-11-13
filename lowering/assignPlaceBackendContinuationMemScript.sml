(* Storage/transient assignment at the post-unwrap boundary. *)
Theory assignPlaceBackendContinuationMem
Ancestors
  assignPlaceNormalizationStateMem assignPlaceStorageSuffixMem
  dynStorageContinuation vyperPlaceStoragePreservation vyperStorageLayoutSafety
  bodyMemAssignTopCopyFacts exprSimProps exprSimLayoutTransport
  stmtLowering exprLoweringProps loweringPosts venomState words arithmetic
  vyperTypeSystem vyperValue vyperTyping valueEncodingProps context compileEnv
  vfmConstants bodySim allocLimits exprSimMemDefs
  assignPlaceNormalizationMem exprSimAlloc placeAssignStagingMem
  placeMemoryCopyEffect fragGasPathMem loweringHalt
  assignPlaceDynStorageRuntime assignPlaceDynStorageControl
  assignPlaceDynStorageLayout emitHelper emitHelperProps fragExec fragGasMode
  venomExecSemantics stmtSimStoreCopy dynStorageState list rich_list stmtLoweringMono
  stmtSimAugAssignPlaceMemory

Theorem backend_storage_region[local]:
  storage_layout_safe cx /\ storage_place_region cx (StoragePlace tr w tv) /\
  0 < type_slot_size tv ==>
  ?mid name keys root rtv path delta.
    declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
    storage_subregion rtv path delta tv /\ w = root+n2w delta /\
    w2n root + type_slot_size rtv <= dimword (:256) /\
    w2n root+delta < dimword (:256) /\
    (!mid' name' keys' root' tv'.
      declared_storage_region cx mid' name' keys' = SOME (tr,root',tv') /\
      (root',tv') <> (root,rtv) ==>
      ranges_disjoint (w2n root) (type_slot_size rtv)
                      (w2n root') (type_slot_size tv'))
Proof
  strip_tac >> drule_all storage_place_region_numeric >> strip_tac >>
  qexistsl_tac [`mid`,`name`,`keys`,`root`,`tv'`,`path`,`delta`] >>
  simp[] >> conj_tac
  >- (metis_tac[word_add_n2w, n2w_w2n]) >>
  rpt strip_tac >>
  irule storage_layout_safe_region_separation >>
  goal_assum (drule_at (Pat `storage_layout_safe _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  metis_tac[pairTheory.PAIR_EQ, optionTheory.SOME_11]
QED

Theorem backend_bytes_cases[local]:
  is_bytestring_type ty <=>
  (?n. ty = BaseT (BytesT (Dynamic n))) \/ (?n. ty = BaseT (StringT n))
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]
QED

Theorem backend_bytes_slots[local]:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv ==>
  0 < type_slot_size stv /\ type_slot_size stv <= type_slot_size dtv
Proof
  strip_tac >>
  gvs[backend_bytes_cases] >>
  gvs[type_widens_to_def, arg_type_fits_def, evaluate_type_def,
      type_slot_size_def, word_size_def] >>
  intLib.COOPER_TAC
QED

Theorem backend_buffer_counts[local]:
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  type_widens_to tenv sty dty /\
  assignable_type tenv sty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\
  bytes = (if is_bytestring_type dty then type_memory_size stv
           else type_memory_size dtv) /\
  n = (if bytes <= 32 then 1 else bytes DIV 32) ==>
  32*n = type_memory_size stv /\ n <= type_slot_size dtv /\
  val_footprint dtv v <= 32*n
Proof
  strip_tac >>
  `0 < type_slot_size stv` by metis_tac[assignable_type_slot_size_pos] >>
  `dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty` by metis_tac[] >>
  pop_assum strip_assume_tac
  >- (`val_footprint stv v <= type_memory_size stv` by metis_tac[val_footprint_le] >>
      gvs[type_memory_size_slots] >> decide_tac) >>
  drule_all backend_bytes_slots >> strip_tac >>
  `val_footprint dtv v <= type_memory_size stv` by
    metis_tac[valueCopyBytesTheory.bytestring_val_footprint_le] >>
  gvs[type_memory_size_slots] >> decide_tac
QED

Theorem backend_fixed_mem[local]:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    src F loc dty sty NONE (type_memory_bytes ce dty) sa = ((),sb) /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  storage_place_region cx (StoragePlace tr w dtv) /\
  write_storage_slot cx tr w dtv v ee = (INL (),ff) /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce sty = type_memory_size stv /\
   type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  qmatch_asmsub_abbrev_tac `compile_assign_value ce dst _ src F loc dty sty NONE msz` >>
  qabbrev_tac `bytes = if is_bytestring_type dty then type_memory_size stv else type_memory_size dtv` >>
  qabbrev_tac `n = if bytes <= 32 then 1 else bytes DIV 32` >>
  `32*n = type_memory_size stv /\ n <= type_slot_size dtv /\
   val_footprint dtv v <= 32*n` by
    (irule backend_buffer_counts >> simp[Abbr `bytes`, Abbr `n`] >> metis_tac[]) >>
  `0 < type_slot_size dtv` by
    (Cases_on `dty = sty` >- (gvs[] >> metis_tac[assignable_type_slot_size_pos]) >>
     metis_tac[backend_bytes_slots, LESS_LESS_EQ_TRANS]) >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    (Cases_on `dty = sty` >- gvs[] >>
     metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]) >>
  `storage_layout_safe cx` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all backend_storage_region >> strip_tac >>
  `well_formed_type_value dtv` by metis_tac[cj 1 evaluate_type_well_formed] >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `w2n sw + 32*n < dimword (:256) /\ n < dimword (:256)` by decide_tac >>
  irule (cj 2 assign_place_storage_suffix_mem) >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  qexistsl_tac [`ee`,`sw`,`INL ()`,`v`] >>
  simp[Abbr `bytes`, Abbr `n`, Abbr `msz`] >>
  gvs[] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem backend_dynamic_mem[local]:
  compile_dynarray_to_storage src dst
    ((type_memory_bytes ce et+31) DIV 32) (type_memory_bytes ce et) tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) et = SOME tv /\ 0 < cap /\
  well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) v /\
  val_in_memory (ArrayTV tv (Dynamic cap)) v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  storage_place_region cx (StoragePlace tr w (ArrayTV tv (Dynamic cap))) /\
  write_storage_slot cx tr w (ArrayTV tv (Dynamic cap)) v ee = (INL (),ff) /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by
    simp[type_slot_size_def] >>
  `storage_layout_safe cx` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all backend_storage_region >> strip_tac >>
  `type_memory_bytes ce et = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `~s.vs_call_ctx.cc_static /\ s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, state_rel_def, alloca_room_next_lt] >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  irule (cj 2 dyn_storage_continuation_mem) >> simp[] >>
  goal_assum (drule_at (Pat `compile_dynarray_to_storage _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  qexistsl_tac [`ee`,`et`,`keys`,`mid`,`name`,`sw`,`INL ()`,`vs`] >> simp[] >>
  gvs[]
QED

Theorem assign_place_normalization_size_bound:
  stmt_exprs_ok ce (Assign (BaseTarget bt) e) /\
  target_store_place ce bt = SOME (SOME (ValPT dty)) /\
  sty = lowered_value_type ce e /\ ~is_word_type dty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  type_memory_bytes ce dty = type_memory_size dtv ==>
  (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
   type_memory_size dtv < dimword (:256))
Proof
  rpt strip_tac >>
  `type_memory_size dtv < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, assign_alloc_ok_def] >>
  gvs[dimword_def]
QED

Theorem backend_physical_store_bound[local]:
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  read_result cx raw ee = (INL v,ee) /\ val_wf stv v /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next ==>
  vv_store_bound cx sty sty ee raw vv s
Proof
  strip_tac >>
  `val_store_size stv v <= type_memory_size stv` by metis_tac[val_store_size_le] >>
  Cases_on `vv` >>
  gvs[vv_store_bound_def, contextTheory.vv_operand_def] >> rpt strip_tac >>
  gvs[] >> decide_tac
QED

Theorem backend_normalization_mem[local]:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty (vv_operand vv) sty sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  type_memory_size dtv < dimword (:256) /\
  vv_at ce cx sty origin sa ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  assignable_type (get_tenv cx) sty /\
  type_widens_to (get_tenv cx) sty dty /\ dty <> sty /\
  ~is_word_type dty /\ ~is_word_type sty /\
  ~is_bytestring_type dty /\ ~is_bytestring_type sty /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t dw. gas_path_mem ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    eval_operand buf.buf_operand t = SOME dw /\
    w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
    alloca_history func t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `vv_store_bound cx sty sty ee raw vv s` by
    (irule backend_physical_store_bound >> metis_tac[]) >>
  drule_all (Q.INST [`ty` |-> `sty`] normalization_allocate) >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[compile_alloc_buffer_parts] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  `compile_store_memory ce (vv_operand vv) buf.buf_operand dty sty sm = ((),sb)` by
    (asm_rewrite_tac[contextTheory.compile_store_memory_def] >> gvs[]) >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv)` by
    (irule compile_store_memory_nonword_effect_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`stv`,`sw`,`get_tenv cx`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule normalization_copy_state >> metis_tac[]) >>
  `t.vs_alloca_next = r.vs_alloca_next` by
    (drule_all typed_copy_effect_record >> simp[venom_state_component_equality]) >>
  `alloca_history func t` by
    (irule normalization_path_history >> simp[] >>
     qexistsl_tac [`ctx`,`0`,`r`] >> gvs[stmt_state_rel_def]) >>
  drule_all typed_copy_effect_endpoint >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand buf.buf_operand t = SOME dw` by
    (gvs[eval_operand_def] >> metis_tac[typed_copy_effect_lookup]) >>
  qexistsl_tac [`t`,`dw`] >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem backend_dynamic_empty_path_mem[local]:
  compile_dynarray_to_storage src dst ew ems tr sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n b + 32 <= s.vs_alloca_next /\ mload (w2n b) s = 0w ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t = (if tr then tstore else sstore) k 0w s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all dyn_storage_compile_phase_certificate >> strip_tac >>
  rename1 `fresh_label "dyn_body" s2 = (loop_body,s3)` >>
  `?entry. gas_marked_path T ctx func s 0 (OK entry) /\
    store_copy_normalize s entry = s /\
    lookup_var cv entry = SOME 0w /\ eval_operand len entry = SOME 0w /\
    (!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s) /\
    ~entry.vs_halted /\ entry.vs_current_bb = hdr /\ entry.vs_inst_idx = 0`
    by suspend "entry" >>
  `?last. gas_marked_path T ctx func entry 0 (OK last) /\
    store_copy_normalize s last = s /\ eval_operand len last = SOME 0w /\
    (!x. not_fresh_at sa x ==> lookup_var x last = lookup_var x s) /\
    ~last.vs_halted /\ last.vs_current_bb = exit /\ last.vs_inst_idx = 0`
    by suspend "header" >>
  suspend "exit"
QED

Resume backend_dynamic_empty_path_mem[entry]:
  drule_all dyn_storage_entry_layout >> strip_tac >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac cs_extends_new_block >>
  `fn_has_code s7 s8 func` by
    (irule fn_has_code_mid >> conj_tac >- metis_tac[cs_extends_trans] >>
     qexistsl_tac [`ex`,`s6`] >> simp[] >> metis_tac[cs_extends_trans]) >>
  drule_all fn_has_code_new_block >> strip_tac >>
  `s7.cs_current_bb = sa.cs_current_bb /\
   s7.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id MLOAD [src] [lv];
     mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [cv];
     mk_inst s6.cs_next_id JMP [Label hdr] []]` by
    (qpat_x_assum `emit_inst JMP _ _ s6 = _` mp_tac >>
     simp[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
          comp_return_def] >> strip_tac >>
     gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     metis_tac[DROP_LENGTH_APPEND, GSYM APPEND_ASSOC]) >>
  `gas_path_mem ctx func s 0
    (OK (jump_to hdr ((update_var cv 0w
      (update_var lv (mload (w2n b) s) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))` by
    (irule assignPlaceDynStoragePathsTheory.dyn_storage_entry_path_mem >> simp[] >>
     qexistsl_tac [`<|bb_label := s7.cs_current_bb;
       bb_instructions := s7.cs_current_insts|>`, `sa.cs_next_id`,
       `sa.cs_next_id+1`, `s6.cs_next_id`, `src`] >>
     gvs[DROP_LENGTH_APPEND]) >>
  drule gas_marked_path_from_mem >>
  disch_then (qspec_then `T` assume_tac) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  simp[store_copy_normalize_def, jump_to_def,
       update_var_def, lookup_var_def, eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> `x <> lv /\ x <> cv` by metis_tac[] >> simp[]
QED

Resume backend_dynamic_empty_path_mem[header]:
  imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac cs_extends_new_block >>
  `fn_has_code s8 b1 func` by
    (irule fn_has_code_mid >> conj_tac >- metis_tac[cs_extends_trans] >>
     qexistsl_tac [`ex`,`s6`] >> simp[] >> metis_tac[cs_extends_trans]) >>
  `s8.cs_next_var = s5.cs_next_var` by
    gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
        comp_return_def, new_block_def] >>
  `s5.cs_next_var <= s8.cs_next_var` by simp[] >>
  drule_all (Q.INST [`mid` |-> `s8`] dyn_storage_entry_live) >> strip_tac >>
  `s8.cs_current_bb = hdr /\ s8.cs_current_insts = []` by
    gvs[new_block_def, comp_return_def] >>
  `?r. gas_marked_path T ctx func entry 0 (OK r) /\
    store_copy_normalize entry r = entry /\
    (!x. not_fresh_at s8 x ==> lookup_var x r = lookup_var x entry) /\
    ~r.vs_halted /\ r.vs_current_bb = exit /\ r.vs_inst_idx = 0` by
    (irule (SRULE [] (Q.INST [`j` |-> `0`, `L` |-> `0`] dyn_storage_header_compile_path_mem)) >>
     simp[eval_operand_def] >>
     qexistsl_tac [`cv`,`done`,`len`,`loop_body`,`lt`,`oldb`,`s9`,`s10`,`s11`,`b1`] >>
     simp[eval_operand_def]) >>
  `store_copy_normalize s r = s` by
    (qpat_x_assum `store_copy_normalize entry r = entry` mp_tac >>
     gvs[store_copy_normalize_def, venom_state_component_equality]) >>
  qexists_tac `r` >> simp[] >> gvs[eval_operand_def] >> metis_tac[]
QED

Resume backend_dynamic_empty_path_mem[exit]:
  `last.vs_call_ctx = s.vs_call_ctx /\ last.vs_labels = s.vs_labels` by
    (qpat_x_assum `store_copy_normalize s last = s` mp_tac >>
     simp[store_copy_normalize_def, venom_state_component_equality]) >>
  `eval_operand dst last = SOME k` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `ex.cs_current_bb = exit /\ ex.cs_current_insts = []` by
    gvs[new_block_def, comp_return_def] >>
  qpat_x_assum `fn_has_code ex sb func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  `sb.cs_current_bb = exit /\
   sb.cs_current_insts =
    [mk_inst ex.cs_next_id (if tr then TSTORE else SSTORE) [dst;len] []]` by
    gvs[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `gas_marked_path T ctx func last 0
    (OK (((if tr then tstore else sstore) k 0w last) with
      vs_inst_idx := last.vs_inst_idx + 1))` by
    (irule assignPlaceDynStoragePathsTheory.dyn_storage_length_store_path_mem >> simp[] >>
     qexistsl_tac [`bb`, `dst`, `ex.cs_next_id`, `len`] >> gvs[]) >>
  `gas_marked_path T ctx func s 0
    (OK (((if tr then tstore else sstore) k 0w last) with
      vs_inst_idx := last.vs_inst_idx + 1))` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  gvs[] >> Cases_on `tr` >> gvs[] >> conj_tac
  >- (qpat_x_assum `store_copy_normalize s last = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      rpt (pop_assum kall_tac) >> simp[store_copy_normalize_def, tstore_def])
  >- fs[tstore_def, lookup_var_def]
  >- (qpat_x_assum `store_copy_normalize s last = _`
        (fn th => once_rewrite_tac [GSYM th]) >>
      rpt (pop_assum kall_tac) >> simp[store_copy_normalize_def, sstore_def]) >>
  fs[sstore_def, lookup_var_def]
QED

Finalise backend_dynamic_empty_path_mem

Theorem backend_dynamic_zero_mem[local]:
  compile_dynarray_to_storage src dst ew ems tr sa = ((),sb) /\
  well_formed_type_value (ArrayTV tv (Dynamic 0)) /\
  value_has_type (ArrayTV tv (Dynamic 0)) v /\
  val_in_memory (ArrayTV tv (Dynamic 0)) v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV tv (Dynamic 0)) <= s.vs_alloca_next /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  storage_place_region cx (StoragePlace tr w (ArrayTV tv (Dynamic 0))) /\
  write_storage_slot cx tr w (ArrayTV tv (Dynamic 0)) v ee = (INL (),ff) /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `v = ArrayV (DynArrayV [])` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `w2n sw + 32 <= s.vs_alloca_next /\ mload (w2n sw) s = 0w` by
    gvs[type_memory_size_slots, type_slot_size_def, val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `~s.vs_call_ctx.cc_static /\ s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, state_rel_def, alloca_room_next_lt] >>
  drule_all backend_dynamic_empty_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic 0))` by simp[type_slot_size_def] >>
  `storage_layout_safe cx` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  drule_all backend_storage_region >> strip_tac >>
  `stmt_state_rel ctx func ce cx ff t` by
    (irule (cj 2 dyn_storage_write_state) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `write_storage_slot _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     qexistsl_tac [`keys`,`mid`,`name`,`sa`] >> simp[COUNT_LIST_def] >>
     gvs[type_memory_size_slots, type_slot_size_def]) >>
  qexists_tac `t` >> simp[]
QED

Theorem backend_direct_mem:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    src F loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et)
      | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\
  well_formed_type_value dtv /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  storage_place_region cx (StoragePlace tr w dtv) /\
  write_storage_slot cx tr w dtv v ee = (INL (),ff) /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?et cap. dty = ArrayT et (Dynamic cap)`
  >- suspend "dynamic" >>
  `(case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et)
      | _ => NONE) = NONE` by
    (Cases_on `dty` >> simp[] >> rename1 `ArrayT et bd` >>
     Cases_on `bd` >> gvs[]) >>
  irule backend_fixed_mem >> metis_tac[]
QED

Resume backend_direct_mem[dynamic]:
  pop_assum strip_assume_tac >> gvs[is_bytestring_type_def] >>
  `?tv. evaluate_type (get_tenv cx) et = SOME tv /\
        dtv = ArrayTV tv (Dynamic cap)` by
    gvs[evaluate_type_def, AllCaseEqs()] >> gvs[] >>
  `compile_dynarray_to_storage src dst
    ((type_memory_bytes ce et+31) DIV 32) (type_memory_bytes ce et) tr sa = ((),sb)` by
    (Cases_on `tr` >>
     gvs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  Cases_on `cap = 0`
  >- (gvs[] >> irule backend_dynamic_zero_mem >> simp[] >>
      goal_assum (drule_at (Pat `compile_dynarray_to_storage _ _ _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
      metis_tac[ADD_COMM]) >>
  `0 < cap` by decide_tac >>
  irule backend_dynamic_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_dynarray_to_storage _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >> metis_tac[]
QED

Finalise backend_direct_mem

Theorem assign_place_backend_continuation_mem:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    (vv_operand vv) F (vv_location vv) dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et)
     | _ => NONE) (type_memory_bytes ce dty) sa = ((),sb) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  well_formed_type_value stv /\ well_formed_type_value dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx sty origin sa ee raw vv s /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ vp => vp.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  eval_operand dst s = SOME w /\
  (!x. vv_operand vv = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  place_ptr_rel ce cx s (PlaceR p) w
    (SOME (if tr then LocTransient else LocStorage)) (Type dty) /\
  storage_place_region cx p /\ expr_sim_inv ce cx env ee /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  stmt_state_rel ctx func ce cx ee s /\
  local_ptrs_reserved ce sa /\ alloca_history func s /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
    type_memory_size dtv < dimword (:256)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p = StoragePlace tr w dtv` by
    (Cases_on `p` >> Cases_on `tr` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     rename1 `StoragePlace b slot tv` >> Cases_on `b` >> gvs[]) >>
  gvs[vyperStateTheory.write_place_def] >>
  Cases_on `dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty`
  >- (irule backend_direct_mem >> simp[] >> metis_tac[]) >>
  suspend "normalize"
QED

Resume assign_place_backend_continuation_mem[normalize]:
  `dty <> sty /\ ~is_bytestring_type dty /\ ~is_bytestring_type sty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `?buf sm sn.
    compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
    compile_store_memory_typed ce buf.buf_operand dty (vv_operand vv) sty sm = ((),sn) /\
    compile_assign_value ce dst (if tr then LocTransient else LocStorage)
      buf.buf_operand F (SOME LocMemory) dty dty
      (case dty of ArrayT et (Dynamic _) =>
        SOME ((type_memory_bytes ce et+31) DIV 32,type_memory_bytes ce et)
       | _ => NONE) (type_memory_bytes ce dty) sn = ((),sb)` by
    (Cases_on `compile_alloc_buffer (type_memory_size dtv) sa` >>
     rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
     Cases_on `compile_store_memory_typed ce buf.buf_operand dty (vv_operand vv) sty sm` >>
     rename1 `compile_store_memory_typed _ _ _ _ _ sm = (u,sn)` >>
     Cases_on `u` >>
     Cases_on `tr` >>
     gvs[compile_assign_value_def, comp_bind_def, comp_return_def,
         AllCaseEqs()] >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  `ci_mono sa sm` by (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sn` by
    metis_tac[CONJUNCT1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono sn sb` by
    metis_tac[CONJUNCT1 ci_mono_stmt_helpers, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (gvs[ci_mono_def] >> rpt conj_tac >>
     (irule fn_has_code_mid >> conj_tac >- simp[] >>
      qexistsl_tac [`sb`,`sa`] >> simp[cs_extends_refl] >>
      metis_tac[cs_extends_trans])) >>
  `type_memory_size dtv < dimword (:256)` by simp[] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by simp[] >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by simp[ADD_COMM] >>
  drule_all backend_normalization_mem >> strip_tac >>
  suspend "suffix"
QED

Resume assign_place_backend_continuation_mem[suffix]:
  `assignable_type (get_tenv cx) dty` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type] >>
  `type_widens_to (get_tenv cx) dty dty` by simp[type_widens_to_def] >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     gvs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_TRANS]) >>
  `!x. buf.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     rpt strip_tac >> gvs[] >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     gvs[ci_mono_def]) >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[aug_place_marked_path_labels, gas_marked_path_from_mem] >>
  `eval_operand dst t = SOME w` by
    (Cases_on `dst` >> gvs[eval_operand_def]) >>
  `?u. gas_marked_path T ctx func t 0 (OK u) /\
    stmt_state_rel ctx func ce cx ff u /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule backend_direct_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     qexistsl_tac [`dtv`,`ee`,`env`,`w`] >> simp[ADD_COMM]
     >- (first_assum ACCEPT_TAC)) >>
  qexists_tac `u` >> simp[]
  >- (gvs[gas_marked_path_def] >>
      metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  metis_tac[]
QED

Finalise assign_place_backend_continuation_mem
