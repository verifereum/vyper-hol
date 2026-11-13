(* Counted sparse storage stores of a captured value, with normalization. *)
Theory assignPlaceBackendContinuationMem
Ancestors
  storeSlotsCountedRun storeSlotsStorageRegion gasPathAllocaHistory
  assignPlaceNormalizationMem assignPlaceNormalizationStateMem
  placeStoreSlots placeStoreStorage vyperPlaceStoragePreservation
  vyperStorageLayoutSafety bodyMemAssignTopCopyFacts exprSimProps
  exprSimLayoutTransport stmtLowering stmtLoweringMono exprLoweringProps
  loweringPosts venomState words arithmetic vyperTypeSystem vyperValue
  vyperTyping valueEncodingProps valueEncodingDefs context compileEnv
  vfmConstants exprSimMemDefs exprSimHypsDefs exprSimHyps
  placeTypedCopyForwardMem placeMemoryCopyEffect fragGasPathMem loweringHalt
  emitHelper emitHelperProps fragExec fragGasMode venomExecSemantics
  stmtSimStoreCopy list rich_list stmtSimAugAssignPlaceMemory
  loweringStateRelDefs freshWrites allocLimits bodySim

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
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv)` by
    (irule typed_memory_rank_forward_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`,`get_tenv cx`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule normalization_copy_state >> metis_tac[]) >>
  `t.vs_alloca_next = r.vs_alloca_next` by
    (drule_all typed_copy_effect_record >> simp[venom_state_component_equality]) >>
  `alloca_history func t` by
    (mp_tac (Q.SPECL [`T`,`ctx`,`func`,`r`,`0`,`t`]
      gas_marked_path_alloca_history) >>
     (impl_tac >- gvs[gas_marked_path_def, stmt_state_rel_def]) >> simp[]) >>
  drule_all typed_copy_effect_endpoint >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand buf.buf_operand t = SOME dw` by
    (gvs[eval_operand_def] >> metis_tac[typed_copy_effect_lookup]) >>
  qexistsl_tac [`t`,`dw`] >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem backend_sparse_direct_mem[local]:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    src F loc dty sty (type_memory_bytes ce dty) sa = ((),sb) /\
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
  local_ptrs_reserved ce sa /\ acyclic_struct_metadata ce.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~(dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty))` by
    metis_tac[] >>
  `compile_store_slots ce src dst dty tr sa = ((),sb)` by
    (Cases_on `tr` >>
     gvs[compile_assign_value_def, comp_bind_def, comp_return_def]) >>
  `0 < type_slot_size dtv` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_assignable_type,
              assignable_type_slot_size_pos] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  drule_all backend_storage_region >> strip_tac >>
  `write_place cx (StoragePlace tr w dtv) v ee = (INL (),ff)` by
    (pure_rewrite_tac [vyperStateTheory.write_place_def] >> first_assum ACCEPT_TAC) >>
  drule_all place_store_storage_write_inv >> strip_tac >>
  `w2n w = w2n root + delta /\
   w2n w + type_slot_size dtv <= dimword (:256)` by
    (drule_all place_store_storage_leaf_bounds >> simp[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def, LESS_EQ_LESS_TRANS] >>
  `type_slot_size stv <= type_slot_size dtv /\
   encode_value stv v = SOME writes /\
   compile_store_slots ce src dst sty tr sa = ((),sb) /\
   val_in_memory dtv v (w2n sw) s.vs_memory` by
    (Cases_on `dty = sty` >- gvs[] >> fs[] >>
     metis_tac[store_slots_bytes_encoding, store_slots_bytes_compile_eq,
               valueCopyBytesTheory.bytestring_val_in_memory_transfer]) >>
  suspend "run"
QED

Resume backend_sparse_direct_mem[run]:
  `w2n w + type_slot_size stv <= dimword (:256)` by decide_tac >>
  mp_tac (Q.SPECL [`type_rank ce.ce_struct_fields sty`, `ce`, `get_tenv cx`,
    `ctx`, `sty`, `stv`, `v`] store_slots_rank_run_mem) >>
  (impl_tac >- (fs[expr_sim_inv_def] >> metis_tac[])) >>
  disch_then (qspecl_then [`src`, `dst`, `tr`, `sa`, `sb`, `func`,
    `s`, `sw`, `w`, `writes`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`, `ks`] strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `ff = _` SUBST1_TAC >>
  irule (SIMP_RULE (srw_ss()) [n2w_w2n]
    (Q.INST [`start` |-> `w2n (w:bytes32)`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
        store_slots_semantic_endpoint_layout)))) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `encode_value dtv v = _`)) >>
  qexistsl_tac [`dty`,`ks`,`s`,`sa`,`sw`] >> gvs[] >> first_assum ACCEPT_TAC
QED

Finalise backend_sparse_direct_mem[local]

Theorem assign_place_backend_continuation_mem:
  compile_assign_value ce dst (if tr then LocTransient else LocStorage)
    (vv_operand vv) F (vv_location vv) dty sty (type_memory_bytes ce dty) sa = ((),sb) /\
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
  >- (irule backend_sparse_direct_mem >> simp[] >> metis_tac[]) >>
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
      buf.buf_operand F (SOME LocMemory) dty dty (type_memory_bytes ce dty) sn = ((),sb)` by
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
    (irule backend_sparse_direct_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     qexistsl_tac [`dtv`,`ee`,`env`,`w`] >> simp[ADD_COMM]
     >- (first_assum ACCEPT_TAC)) >>
  qexists_tac `u` >> simp[]
  >- (gvs[gas_marked_path_def] >>
      metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  metis_tac[]
QED

Finalise assign_place_backend_continuation_mem
