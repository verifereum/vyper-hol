Theory bodyPtrIfExpBytesAllocate
Ancestors
  bodyPtrIfExpAllocOrdered bodyPtrIfExpBytesConsumer bodyPtrIfExpNoopPost
  bodyPtrIfExpBytesResources bodyPtrIfExpAllocCaller bodyPtrIfExpBytesEndpoint
  bodyPtrDefs exprSimBufferStore exprSimProps exprSimDefs exprLoweringProps
  loweringPosts compileEnv fragExec fragGasPathPtr gasSummaryComposePtr
  venomState venomInst finite_map words rich_list loweringHalt

Theorem ifexp_allocate_unwrap_bytes:
  vv_post ctx fn ce cx arm es sa sb s0 ee raw vv s /\
  stmt_state_rel ctx fn ce cx es s0 /\
  ghost_inv d ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer capacity sb = (buf,sc) /\ fn_has_code sb sc fn /\
  compile_store_bytestring (vv_operand vv) buf.buf_operand sc = ((),sd) /\
  fn_has_code sc sd fn /\ capacity < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  ptr_vv_ok cx (expr_type arm) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type arm) ==>
    ptr_buf_ok ce arm op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce arm p.ptr_operand G s) /\
  ((?ty op. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sc = (vv_operand vv,sc) /\
  read_result cx raw ee = (INL v,ee) /\
  is_bytestring_type (expr_type arm) /\ is_bytestring_type (expr_type result) /\
  evaluate_type (get_tenv cx) (expr_type arm) = SOME stv /\
  evaluate_type (get_tenv cx) (expr_type result) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  val_store_size stv v = 32 + 32 * ((len+31) DIV 32) /\
  val_footprint dtv v <= capacity /\ val_store_size dtv v <= capacity /\
  type_memory_bytes ce (lowered_value_type ce result) <= capacity /\
  32 + 32 * ((len+31) DIV 32) <= capacity /\ len+31 < dimword(:256) ==>
  ?out Gf tnf q.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK q) /\
    expr_post ctx fn ce cx result es sa sd s0 ee v (Var out) q /\
    ghost_inv d ce cx ee Gf tnf q /\ ghost_kept ce es sa G0 tn0 s0 Gf tnf /\
    ptr_val_ok cx (expr_type result) v (Var out) Gf tnf q /\
    ptr_buf_ok ce result (Var out) Gf q /\
    q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
    ~q.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_alloc_buffer_vv_ordered_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `~is_word_type (expr_type arm)` by metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  drule_all unwrap_value_noop_post >> strip_tac >>
  `?w. eval_operand (vv_operand vv) t = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def]) >>
  drule_all ifexp_bytes_writer_resources >> strip_tac >>
  `local_ptrs_reserved ce sc` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >> decide_tac) >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  suspend "writer"
QED

Resume ifexp_allocate_unwrap_bytes[writer]:
  `sc.cs_current_bb = sd.cs_current_bb` by gvs[same_blocks_def] >>
  `?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sc sd) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sc sd fn` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >> qexists_tac `bb` >>
     gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `not_fresh_at sc p` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sb` >>
     simp[] >> metis_tac[]) >>
  `not_fresh_at sc out /\ sa.cs_next_var <= sc.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     gvs[not_fresh_at_def] >> decide_tac) >>
  `sb.cs_next_id < sd.cs_next_id` by decide_tac >>
  `32 + 32 * ((len+31) DIV 32) < dimword(:256)` by decide_tac >>
  `compile_store_bytestring (Var p) (Var out) sc = ((),sd)` by metis_tac[] >>
  `FLOOKUP t.vs_allocas sb.cs_next_id =
     SOME (w2n (n2w (buffer_allocation_base s sb.cs_next_id) : bytes32),capacity)` by simp[] >>
  `!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= w2n (n2w (buffer_allocation_base s sb.cs_next_id) : bytes32) \/
    w2n (n2w (buffer_allocation_base s sb.cs_next_id) : bytes32)+capacity <= p` by
      asm_rewrite_tac[] >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n (n2w (buffer_allocation_base s sb.cs_next_id) : bytes32) \/
    w2n (n2w (buffer_allocation_base s sb.cs_next_id) : bytes32)+capacity <= off` by
      asm_rewrite_tac[] >>
  `32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32)` by simp[] >>
  drule_all ifexp_allocated_bytes_writer >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32)` kall_tac >>
  qpat_x_assum `sc = sc` kall_tac >>
  qexistsl_tac [`out`, `Gf`, `tnf`,
    `sf with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sc sd)`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  qpat_x_assum `sf with <|vs_vars := _; vs_memory := _|> = t` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >> simp[]
QED

Finalise ifexp_allocate_unwrap_bytes
