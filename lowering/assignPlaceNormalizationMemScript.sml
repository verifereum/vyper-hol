Theory assignPlaceNormalizationMem
Ancestors
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

Theorem normalization_edge_history[local]:
  gas_path_mem_edge ctx func s n (OK u) /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s ==> alloca_history func u
Proof
  rw[gas_path_mem_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >>~- ([`exit_result _`],
        qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
        gvs[fragExecTheory.exit_result_def])
  >> drule_all allocaHistoryTheory.alloca_history_step >> simp[] >>
  strip_tac >> metis_tac[history_phi_entry]
QED

Theorem normalization_path_history:
  gas_path_mem ctx func s n (OK u) /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_history func s ==> alloca_history func u
Proof
  `!ctx func s n result. gas_path_mem ctx func s n result ==>
     !u. result = OK u ==> fn_inst_ids_distinct func ==>
     alloca_inv s ==> alloca_history func s ==> alloca_history func u`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[normalization_edge_history, aggregate_mem_edge_alloca_inv,
            fragExecTheory.exit_result_def]
QED

(* The callback is exactly the tight nonword store contract.  Its caller
   supplies the proved store theorem; no new compilation judgment is hidden. *)
Theorem assign_place_normalization_mem:
  (!dty sty tenv dtv stv cenv v sw u dw dp sp a b func ctx.
    ~is_word_type dty /\ ~is_word_type sty /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) /\
    fn_inst_ids_distinct func /\
    (dty <> sty /\ ~is_bytestring_type dty ==>
      w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size dtv <= w2n sw) /\
    compile_store_memory cenv sp dp dty sty a = ((),b) ==>
    ?t. gas_path_mem ctx func u 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)) ==>
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ty (vv_operand vv) sty sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx ee s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  type_memory_size dtv < dimword (:256) /\
  vv_at ce cx sty origin sa ee raw vv s /\
  vv_store_bound cx ty sty ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  assignable_type (get_tenv cx) sty /\
  type_widens_to (get_tenv cx) sty ty /\ ty <> sty /\
  ~is_word_type ty /\ ~is_word_type sty /\
  ~is_bytestring_type ty /\ ~is_bytestring_type sty /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r t dw. gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    eval_operand buf.buf_operand t = SOME dw /\
    w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_history func t /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n dw,type_memory_size dtv) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK r) /\
    typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv)
Proof
  disch_then (mk_asm "copy") >> strip_tac >>
  drule_all normalization_allocate >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_parts] >>
  `compile_store_memory ce (vv_operand vv) buf.buf_operand ty sty sm = ((),sb)` by
    (asm_rewrite_tac[contextTheory.compile_store_memory_def] >> gvs[]) >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv)` by
    (asm "copy" irule >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`stv`,`sw`,`get_tenv cx`] >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  asm_x "copy" kall_tac >>
  `t.vs_alloca_next = r.vs_alloca_next` by
    (drule_all typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `alloca_history func t` by
    (irule normalization_path_history >> simp[] >>
     qexistsl_tac [`ctx`,`0`,`r`] >>
     gvs[stmt_state_rel_def]) >>
  drule_all typed_copy_effect_endpoint >> strip_tac >>
  drule_all typed_copy_effect_allocas >> disch_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand buf.buf_operand t = SOME dw` by
    (gvs[eval_operand_def] >> metis_tac[typed_copy_effect_lookup]) >>
  qexistsl_tac [`r`,`t`,`dw`] >> asm_simp_tac (srw_ss()) [] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
