(* Layout and composition boundaries for the allocation/unwrap prefix. *)
Theory abiEncTuplePtrMaterializeOwned
Ancestors
  abiEncTuplePtrMaterializePrefix abiEncTuplePtrMaterializeCode
  abiEncodeArgsCase loweringPosts exprLowering vyperAST exprSimProps
  loweringStateRelDefs exprPtrUnwrapCodeCopyMarked exprPtrUnwrapCodeEdges
  valueEncodingProps exprSimMemorySource exprPtrUnwrapCode exprPtrUnwrapTypedSize
  valueEncodingTyping vyperState words exprPtrUnwrapStorageLayout
  bodyPtrDefs exprSimUnwrap exprPtrUnwrapMarked gasSummaryComposePtr
  exprSimUnwrapProps abiEncTuplePtrMaterializeStorage
  abiEncTuplePtrMaterializeAlloc exprLoweringProps compileEnv context
  fragGasPathPtr logGhostFramePtr loweringHalt

Theorem materialize_lowered_physical_capacity:
  !ce e. arg_type_fits (lowered_value_type ce e) (expr_type e) ==>
    type_memory_bytes ce (lowered_value_type ce e) <=
      type_memory_bytes ce (post_value_type ce e)
Proof
  rpt strip_tac >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, expr_type_def] >> IF_CASES_TAC >> simp[]) >>
  gvs[] >> metis_tac[cj 1 abi_args_fits_memory_bytes]
QED

Theorem materialize_physical_post_start:
  expr_post ctx fn ce cx e ee sm sb s ee v op z /\
  sa.cs_next_id <= sm.cs_next_id ==>
  expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    sb s ee v op z
Proof
  rw[expr_post_def, wb_frame_def]
  >- (irule expr_val_at_start_mono >> qexists `sm` >> simp[])
  >- (irule expr_val_own_start_mono >> qexists `sm` >> simp[])
  >- (gvs[not_fresh_at_def] >> first_x_assum irule >> simp[])
  >- (qpat_x_assum `!aid off sz. _` irule >>
      conj_tac >- (first_assum ACCEPT_TAC) >> qexists `aid` >> simp[] >> decide_tac) >>
  qpat_x_assum `~expr_has_effect e ==> _` mp_tac >>
  simp[pure_frame_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!n b sz. _` irule >> qexists `n` >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!off len. _` irule >>
  rpt strip_tac >> qpat_x_assum `!inst b sz. _` irule >>
  qexists `inst` >> simp[] >> decide_tac
QED

(* Compiler and physical-layout premises for the code branch; the execution
   itself remains in materialize_code_unwrap_owned_ptr. *)
Theorem materialize_code_physical_layout:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  ~is_word_type (post_value_type ce e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
    type_memory_size ty < 2**64) ==>
  t = post_value_type ce e /\
  compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes ce t)
    ((type_memory_bytes ce t+31) DIV 32) F ce.ce_imm_alloca sm = (op,sb) /\
  32*((type_memory_bytes ce t+31) DIV 32) = type_memory_bytes ce t /\
  type_memory_bytes ce t < dimword (:256) /\
  type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce t /\
  ?ty v. evaluate_type (get_tenv cx) t = SOME ty /\ val_wf ty v /\
    read_result cx raw ee = (INL v,ee)
Proof
  strip_tac >> drule_all vv_post_code_source >> strip_tac >> gvs[] >>
  `?ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty /\
         val_wf ty v` by
    (gvs[immutable_holds_def, read_result_def, return_def] >>
     metis_tac[value_has_type_val_wf]) >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
   type_memory_size ty < 2**64` by (simp[] >> metis_tac[]) >>
  `32*((type_memory_bytes ce (post_value_type ce e)+31) DIV 32) =
     type_memory_bytes ce (post_value_type ce e)` by
    metis_tac[unwrap_typed_buffer_count, type_memory_size_slots] >>
  `type_memory_bytes ce (post_value_type ce e) < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce (post_value_type ce e)` by
    metis_tac[materialize_lowered_physical_capacity] >>
  simp[] >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_runtime_code_route]
QED

Theorem materialize_slot_physical_input:
  vv_post ctx fn ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  p.ptr_location = slot_loc tr /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s ==>
  t = post_value_type ce e /\
  ?w. eval_operand p.ptr_operand s = SOME w /\
    storage_holds cx tr (post_value_type ce e) raw w ee s /\
    op_taint tn p.ptr_operand = {}
Proof
  Cases_on `tr` >>
  simp[slot_loc_def, vv_post_def, vv_holds_def, ptr_vv_ok_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem materialize_slot_physical_layout:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = slot_loc tr /\ ~is_word_type t /\
  storage_holds cx tr t raw w ee s /\
  type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce t /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes ce t = type_memory_size ty /\ type_memory_size ty < 2**64) ==>
  ?ty. evaluate_type (get_tenv cx) t = SOME ty /\
    compile_ensure_in_memory p.ptr_operand (slot_loc tr) (type_memory_bytes ce t)
      (type_slot_size ty) ce.ce_is_ctor ce.ce_imm_alloca sm = (op,sb) /\
    sm.cs_next_id < sb.cs_next_id /\
    type_memory_size ty <= type_memory_bytes ce t /\
    32*type_slot_size ty <= type_memory_bytes ce t /\
    type_memory_bytes ce t < dimword (:256) /\ type_slot_size ty < 2**256
Proof
  strip_tac >> drule unwrap_storage_evaluated_type >> strip_tac >>
  `type_memory_bytes ce t = type_memory_size tv /\
   type_memory_size tv < 2**64` by simp[] >>
  drule_all unwrap_slot_ensure_layout >> strip_tac >>
  `((type_memory_bytes ce t+31) DIV 32) = type_slot_size tv` by
    metis_tac[unwrap_typed_buffer_count] >>
  `type_slot_size tv < 2**256` by
    (irule unwrap_typed_buffer_count_bound >> simp[]) >>
  `type_memory_bytes ce t < dimword (:256)` by
    (gvs[dimword_def] >> decide_tac) >>
  qexists `tv` >> gvs[type_memory_size_slots]
QED

Theorem materialize_physical_unwrap_owned_ptr:
  unwrap_value ce vv sm = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  sa.cs_next_id <= sm.cs_next_id /\
  ~is_word_type (post_value_type ce e) /\ ~ce.ce_is_ctor /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
    type_memory_size ty < 2**64) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved ce sm /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op ==> ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv ret ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  not_fresh_at sm dst /\ lookup_var dst s = SOME dw /\
  FLOOKUP s.vs_allocas aid = SOME row /\ ptr_covers G tn dst s capacity ==>
  ?H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (read_result cx raw)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret ce cx ee H tf z /\
    ptr_val_ok cx (post_value_type ce e) v op H tf z /\ ptr_buf_ok ce e op H z /\
    ghost_kept ce ee sm G tn s H tf /\
    lookup_var dst z = SOME dw /\ FLOOKUP z.vs_allocas aid = SOME row /\
    ptr_covers H tf dst z capacity
Proof
  strip_tac >> Cases_on `vv`
  >- suspend "noop_stack" >>
  rename1 `LocatedValue t p` >>
  `~is_word_type t` by
    metis_tac[vv_post_located_type, valueCopyBytesTheory.is_bytestring_word_type] >>
  `p.ptr_location <> LocCalldata` by metis_tac[vv_post_not_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "noop_memory" >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >>
  `?tr. p.ptr_location = slot_loc tr` by
    (Cases_on `p.ptr_location` >> gvs[slot_loc_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> suspend "slot"
QED

Resume materialize_physical_unwrap_owned_ptr[noop_stack]:
  drule_at (Pat `unwrap_value _ _ _ = _`)
    (SRULE[] (Q.INST [`R` |-> `\sm G tn s. ghost_inv ret ce cx ee G tn s`,
      `D` |-> `cx_dead cx`, `PG` |-> `PG`] materialize_noop_physical_ptr_frame)) >>
  simp[] >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`tn`, `ret`, `PG`, `G`] mp_tac) >>
  gvs[] >> strip_tac >> gvs[] >>
  drule read_result_gas_obs >> strip_tac >>
  qexistsl [`G`, `tn`, `s`] >>
  simp[gas_marked_exec_ptr_def, ghost_kept_def]
QED

Resume materialize_physical_unwrap_owned_ptr[noop_memory]:
  drule_at (Pat `unwrap_value _ _ _ = _`)
    (SRULE[] (Q.INST [`R` |-> `\sm G tn s. ghost_inv ret ce cx ee G tn s`,
      `D` |-> `cx_dead cx`, `PG` |-> `PG`] materialize_noop_physical_ptr_frame)) >>
  simp[] >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`tn`, `ret`, `PG`, `G`] mp_tac) >>
  gvs[] >> strip_tac >> gvs[] >>
  drule read_result_gas_obs >> strip_tac >>
  qexistsl [`G`, `tn`, `s`] >>
  simp[gas_marked_exec_ptr_def, ghost_kept_def]
QED

Resume materialize_physical_unwrap_owned_ptr[code]:
  drule_all materialize_code_physical_layout >> strip_tac >> gvs[] >>
  drule_all vv_post_read_result >> strip_tac >>
  `ptr_vv_ok cx (post_value_type ce e) (Value v)
     (LocatedValue (post_value_type ce e) p) ee G tn s` by
    gvs[ptr_vv_ok_def] >>
  `(!ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size ty)` by
    (rpt strip_tac >> gvs[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    gvs[contextTheory.vv_operand_def] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) materialize_code_unwrap_owned_ptr >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all materialize_physical_post_start >> strip_tac >>
  drule read_result_gas_obs >> strip_tac >>
  qexistsl [`H`, `tf`, `z`] >> gvs[gas_marked_exec_ptr_def]
QED

Resume materialize_physical_unwrap_owned_ptr[slot]:
  drule_all materialize_slot_physical_input >> strip_tac >> gvs[] >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce (post_value_type ce e)` by
    metis_tac[materialize_lowered_physical_capacity] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) materialize_slot_physical_layout >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    gvs[contextTheory.vv_operand_def] >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)
    materialize_storage_unwrap_owned_ptr >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all materialize_physical_post_start >> strip_tac >>
  drule read_result_gas_obs >> strip_tac >>
  qexistsl [`H`, `tf`, `z`] >> gvs[gas_marked_exec_ptr_def]
QED
Finalise materialize_physical_unwrap_owned_ptr

Theorem materialize_alloc_unwrap_owned_ptr:
  stmt_state_rel ctx fn ce cx es s0 /\
  compile_alloc_buffer n sm = (buf,sn) /\
  unwrap_value ce vv sn = (op,sb) /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ghost_inv ret ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_has_code sm sn fn /\ fn_has_code sn sb fn /\ fn_inst_ids_distinct fn /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type ce e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size ty /\
    type_memory_size ty < 2**64) /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op ==> ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) ==>
  ?dst u H tf z.
    buf.buf_operand = Var dst /\
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H tf (OK z) /\
    vv_post ctx fn ce cx e es sa sn s0 ee raw vv u /\
    expr_post ctx fn ce cx e ee (sa with cs_next_var := sn.cs_next_var)
      sb u ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret ce cx ee H tf z /\ ghost_kept ce es sa G0 tn0 s0 H tf /\
    ptr_val_ok cx (post_value_type ce e) v op H tf z /\ ptr_buf_ok ce e op H z /\
    lookup_var dst z = SOME (n2w (buffer_allocation_base s sm.cs_next_id)) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (buffer_allocation_base s sm.cs_next_id,n) /\
    ptr_covers H tf dst z n /\
    buffer_allocation_base s sm.cs_next_id + n < dimword (:256) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= buffer_allocation_base s sm.cs_next_id \/
      buffer_allocation_base s sm.cs_next_id+n <= off) /\
    (!name p sz. local_region ce es.scopes s0 name p sz ==>
      p+sz <= buffer_allocation_base s sm.cs_next_id \/
      buffer_allocation_base s sm.cs_next_id+n <= p) /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sn.cs_next_id /\
    not_local_ptr ce ee.scopes dst
Proof
  strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) materialize_alloc_physical_ordered_frame >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >>
  suspend "unwrap"
QED

Resume materialize_alloc_unwrap_owned_ptr[unwrap]:
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
   not_fresh_at sn out /\
   (!x. not_fresh_at sm x ==> not_fresh_at sn x)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[] >> decide_tac) >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by metis_tac[] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ sm _ _ _ _ _` kall_tac >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ G tn s` kall_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ G tn s` kall_tac >>
  gvs[] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) materialize_physical_unwrap_owned_ptr >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "join"
QED
Resume materialize_alloc_unwrap_owned_ptr[join]:
  `wb_frame ce es ee sa s0 t` by (gvs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `ghost_kept ce es sa G0 tn0 s0 H tf` by
    (irule ghost_kept_wb_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`ctx`, `cx`, `fn`] >> simp[]) >>
     qexistsl [`G1`, `ee`, `ee`, `t`, `sn`, `tn1`] >>
     simp[] >> decide_tac) >>
  gvs[gas_marked_exec_ptr_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H tf (OK z)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl [`t`, `H`, `tf`, `z`] >> simp[] >> metis_tac[]
QED
Finalise materialize_alloc_unwrap_owned_ptr
