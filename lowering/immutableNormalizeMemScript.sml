(* Framed allocation and typed normalization before an immutable write. *)
Theory immutableNormalizeMem
Ancestors
  immutableNormalizePathMem

Theorem immutable_normalize_mem_endpoint:
  compile_alloc_buffer (type_memory_bytes ce dty) sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sb) /\
  fn_has_code sm mid func /\ fn_has_code mid sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  expr_val_at ce cx sty sa sm es v src s /\ expr_val_rel cx sty v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  type_memory_bytes ce dty < dimword (:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (emitted_blocks mid sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ eval_operand src s = SOME p /\
  (!x. src = Var x ==> not_fresh_at sm x) ==>
  ?dtv u t b. evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ mem_cont_sim ctx func s u /\
    mem_cont_sim ctx func u t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    val_in_memory dtv v b t.vs_memory /\
    b + type_memory_size dtv <= t.vs_alloca_next /\
    b + type_memory_size dtv < dimword (:256) /\
    (w2n p + type_memory_size stv <= b \/
      b + type_memory_size dtv <= w2n p) /\
    alloca_inv t /\ alloca_room ctx func t /\
    t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\
    (!q k. q+k <= b \/ b+type_memory_size dtv <= q ==>
       mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := mid.cs_current_bb; vs_inst_idx := LENGTH mid.cs_current_insts;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    exec_alloca (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes ce dty))]
      [STRING #"%" (toString sm.cs_next_var)]) s
      (n2w (type_memory_bytes ce dty) : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,type_memory_size dtv)
Proof
  strip_tac >> drule_all immutable_normalize_mem_path_endpoint >>
  disch_then (qx_choose_then `dtv` (qx_choose_then `u`
    (qx_choose_then `t` (qx_choose_then `b` strip_assume_tac)))) >>
  qexistsl_tac [`dtv`, `u`, `t`, `b`] >> simp[]
QED
