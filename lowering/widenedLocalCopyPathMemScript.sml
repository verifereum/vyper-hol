(* Counted normalization of a staged aggregate into a reserved local. *)
Theory widenedLocalCopyPathMem
Ancestors
  stagedLocalRegionCopyMem widenedStagingState fragGasPathResources typedNormalizeRankPathMem freshWrites
  abiDecoderFrame compileEnv context stmtLowering venomState words
  abiBuiltinAllocation emitHelperProps exprLoweringProps loweringHalt
  abiTupleProps fragGasPathMem list rich_list arithmetic

Theorem staged_local_typed_copy_path_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  compile_store_memory_typed ce dst dty buf.buf_operand sty sn = ((),sb) /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ alloca_history fn s /\
  fn_has_code sa sn fn /\ fn_has_code sn sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n = type_memory_size stv /\ n < dimword(:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id /\
  type_memory_size dtv <= sz /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r u t (tw:256 word) g.
    gas_path_mem ctx fn s 0 (OK u) /\ gas_path_mem ctx fn s g (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx es r /\ r.vs_memory = s.vs_memory /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    s.vs_alloca_next <= r.vs_alloca_next /\
    (t with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_current_bb := r.vs_current_bb; vs_inst_idx := r.vs_inst_idx;
      vs_prev_bb := r.vs_prev_bb|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a k. (a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
      (a+k <= w2n tw \/ w2n tw+n <= a) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    stmt_state_rel ctx fn ce cx es u /\ alloca_history fn u /\
    alloca_history fn t /\ LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    (!a k. a+k <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory)
Proof
  strip_tac >>
  Q.SUBGOAL_THEN
    `(?aid. FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
       aid < sa.cs_next_id) \/
     (?name. local_region ce es.scopes s name (w2n dw) sz)` assume_tac >-
    (disj1_tac >> qexists `aid` >> simp[]) >>
  drule_all staged_region_typed_copy_path_mem >>
  disch_then (qx_choose_then `r` (qx_choose_then `u` (qx_choose_then `t`
    (qx_choose_then `tw` (qx_choose_then `g` strip_assume_tac))))) >>
  qexistsl [`r`, `u`, `t`, `tw`, `g`] >> gvs[ADD_COMM] >> asm_rewrite_tac[]
QED
