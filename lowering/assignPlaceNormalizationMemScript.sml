Theory assignPlaceNormalizationMem
Ancestors
  bodyMemBopRestWordPath
  loweringStateRelDefs valueEncodingDefs
  exprSimMemUnwrap exprSimAggregateChildren exprSimCopy placeMemoryCopyEffect
  valueCopy exprLoweringProps exprSimAlloc compileEnv venomState fragGasPathMem
  loweringPosts exprSimMemDefs exprSimProps allocaHistoryFragment
  vyperTypeSystem valueEncodingProps bodyMemAggregatePath allocaHistory

(* Allocation-site separation uses full nonbytes footprints, not just the
   bytes occupied by a particular value. *)
Theorem normalization_source_separation[local]:
  vv_at ce cx sty origin sa ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
  (!aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint d n b len) /\
  (!name b len. local_region ce ee.scopes r name b len ==>
    regions_disjoint d n b len) ==>
  type_memory_size stv = 0 \/
  w2n sw + type_memory_size stv <= d \/ d + n <= w2n sw
Proof
  strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  `(?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= w2n sw /\
      w2n sw + type_memory_size stv <= b + sz) \/
   (?name b sz. local_region ce ee.scopes s name b sz /\
      b <= w2n sw /\ w2n sw + type_memory_size stv <= b + sz) \/
   type_memory_size stv = 0` by
    (Cases_on `vv` >>
     gvs[vv_at_def, expr_val_at_def, contextTheory.vv_operand_def] >>
     metis_tac[]) >>
  pop_assum strip_assume_tac
  >- (first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac)
  >- (`local_region ce ee.scopes r name b sz` by
        metis_tac[copy_buffer_local_region_frame] >>
      first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Theorem normalization_source_capacity[local]:
  vv_store_bound cx ty sty ee raw vv s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  assignable_type (get_tenv cx) sty /\ ~is_word_type ty /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw ==>
  0 < type_memory_size stv /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next
Proof
  strip_tac >>
  `0 < type_slot_size stv` by metis_tac[assignable_type_slot_size_pos] >>
  `0 < type_memory_size stv` by simp[type_memory_size_slots] >>
  Cases_on `vv` >>
  gvs[vv_store_bound_def, contextTheory.vv_operand_def] >> metis_tac[]
QED

Theorem normalization_allocate:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx ee s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  type_memory_size dtv < dimword (:256) /\
  vv_at ce cx sty origin sa ee raw vv s /\
  vv_store_bound cx ty sty ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  assignable_type (get_tenv cx) sty /\
  ~is_word_type ty /\ ~is_word_type sty /\ ~is_bytestring_type sty /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r dw. gas_path_mem ctx func s 0 (OK r) /\
    stmt_state_rel ctx func ce cx ee r /\ alloca_history func r /\
    r.vs_memory = s.vs_memory /\ s.vs_alloca_next <= r.vs_alloca_next /\
    eval_operand (vv_operand vv) r = SOME sw /\
    eval_operand buf.buf_operand r = SOME dw /\
    FLOOKUP r.vs_allocas sa.cs_next_id =
      SOME (w2n dw,type_memory_size dtv) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n dw + type_memory_size dtv <= r.vs_alloca_next /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n sw + type_memory_size stv <= r.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  drule_all normalization_source_capacity >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `type_memory_size stv = 0 \/
   w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `u = _` kall_tac >>
     irule normalization_source_separation >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`u`,`v`] >> simp[] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `u = _` kall_tac >>
  qexistsl_tac [`u`,`w`] >> simp[] >> decide_tac
QED

