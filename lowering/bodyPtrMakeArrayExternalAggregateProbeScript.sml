(* Compiler seam probe for runtime immutable aggregate materialization. *)
Theory bodyPtrMakeArrayExternalAggregateProbe
Ancestors
  bodyPtrMakeArrayImmutableAlloc exprLowering context compileEnv
  venomState bodyPtrDefs

Theorem unwrap_runtime_aggregate_split:
  unwrap_value cenv (LocatedValue t p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type t /\ ~cenv.ce_is_ctor /\
  type_memory_bytes cenv t = type_memory_size tv /\
  (type_memory_size tv + 31) DIV 32 = type_slot_size tv ==>
  ?buf sm.
    compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
    compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand
      buf.buf_operand (type_slot_size tv) 0 sm = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >>
  gvs[unwrap_value_def, compile_ensure_in_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem unwrap_runtime_aggregate_ptr_probe:
  unwrap_value cenv (LocatedValue t p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type t /\ ~cenv.ce_is_ctor /\
  type_memory_bytes cenv t = type_memory_size tv /\
  (type_memory_size tv + 31) DIV 32 = type_slot_size tv /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ type_memory_size tv < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
  compile_imm_copy_to_memory F cenv.ce_imm_alloca p.ptr_operand
    buf.buf_operand (type_slot_size tv) 0 sm = ((),sb) /\
  isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  copy_old_operand sa p.ptr_operand /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  immutable_holds cenv cx t (Value v) a es s /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  ?sf Gf tnf root w.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    op = Var root /\ lookup_var root sf = SOME w /\
    ptr_covers Gf tnf root sf (type_memory_size tv) /\
    val_wf tv v /\ val_footprint tv v <= type_memory_size tv /\
    (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem)
Proof
  strip_tac >>
  `op = buf.buf_operand` by
    gvs[unwrap_value_def, compile_ensure_in_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  drule_all immutable_allocated_buffer_ptr_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`z with vs_inst_idx := SUC s.vs_inst_idx + LENGTH (emitted_insts sm sb)`,
    `Gf`, `tnf`, `root`, `w`] >>
  gvs[lookup_var_def, ptr_covers_def]
QED
