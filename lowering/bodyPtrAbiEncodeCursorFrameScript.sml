Theory bodyPtrAbiEncodeCursorFrame
Ancestors
  bodyPtrAbiEncodeCursor bodyPtrDefs exprLoweringProps emitHelperProps
  compileEnv ptrDiscipline ptrSafeRun venomExecSemantics venomState
  finite_map words arithmetic

(* Conjunction abbreviation hiding repeated read-only runtime and ghost fields.
   inst_idx is deliberately absent: counted endpoints advance the PC.
   This frame is not asserted for stores or recursive encoders with writes. *)
Definition abi_encode_read_frame_def:
  abi_encode_read_frame st s G tn t H un <=>
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_labels = s.vs_labels /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\ un.t_trans = tn.t_trans /\
    (!q. not_fresh_at st q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
      op_taint un (Var q) = op_taint tn (Var q))
End

Theorem abi_encode_read_frame_refl[simp]:
  abi_encode_read_frame st s G tn s G tn
Proof
  simp[abi_encode_read_frame_def]
QED

Theorem abi_encode_read_frame_then:
  abi_encode_read_frame st s G tn t H un /\
  abi_encode_read_frame mid t H un u J vn /\
  st.cs_next_var <= mid.cs_next_var ==>
  abi_encode_read_frame st s G tn u J vn
Proof
  simp[abi_encode_read_frame_def] >> rpt strip_tac >>
  `not_fresh_at mid q` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem abi_encode_read_frame_lookup:
  abi_encode_read_frame st s G tn t H un /\ not_fresh_at st q ==>
  lookup_var q t = lookup_var q s
Proof
  simp[abi_encode_read_frame_def]
QED

Theorem abi_encode_read_frame_taint:
  abi_encode_read_frame st s G tn t H un /\ not_fresh_at st q ==>
  op_taint un (Var q) = op_taint tn (Var q)
Proof
  simp[abi_encode_read_frame_def]
QED

Theorem abi_encode_read_frame_covers:
  abi_encode_read_frame st s G tn t H un /\ not_fresh_at st q /\
  ptr_covers G tn q s n ==>
  ptr_covers H un q t n
Proof
  simp[abi_encode_read_frame_def, ptr_covers_def] >> metis_tac[]
QED

Theorem abi_encode_read_frame_clean:
  abi_encode_read_frame st s G tn t H un /\
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) ==>
  (!i. a <= i /\ i < a+n ==> i NOTIN un.t_mem)
Proof
  simp[abi_encode_read_frame_def]
QED

Theorem abi_encode_read_frame_mload:
  abi_encode_read_frame st s G tn t H un ==>
  mload a t = mload a s
Proof
  simp[abi_encode_read_frame_def, mload_def]
QED

Theorem abi_encode_read_frame_control:
  abi_encode_read_frame st s G tn t H un /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  ~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb
Proof
  simp[abi_encode_read_frame_def]
QED

Theorem abi_encode_scalar_add_framed_path:
  !op st st' root right s a G tn total off n ctx D fn PG bb limit_st.
  emit_op ADD [Var root;right] st = (op,st') /\
  not_fresh_at st root /\ lookup_var root s = SOME a /\
  eval_operand right s = SOME (n2w off) /\
  op_taint tn (Var root) = {} /\ op_taint tn right = {} /\
  off+n <= total /\
  (0<n ==> ptr_covers G tn root s total /\ w2n a+off < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME (a+n2w off) /\ op_taint un (Var p) = {} /\
    (0<n ==> ptr_covers H un p t n) /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_inst_idx = s.vs_inst_idx+1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_scalar_add_checked_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`p`, `t with vs_inst_idx := s.vs_inst_idx+1`, `Gf`, `tnf`] >>
  fs[abi_encode_read_frame_def, fresh_vars_wrt_def, lookup_var_def]
QED

Theorem abi_encode_cursor_load_framed_path:
  !op st st' cursor s a G tn ctx D fn PG bb limit_st.
  emit_op MLOAD [Var cursor] st = (op,st') /\
  lookup_var cursor s = SOME a /\ ptr_covers G tn cursor s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME (mload (w2n a) s) /\ op_taint un (Var p) = {} /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_inst_idx = s.vs_inst_idx+1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_cursor_load_checked_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`p`, `t with vs_inst_idx := s.vs_inst_idx+1`, `Gf`, `tnf`] >>
  fs[abi_encode_read_frame_def, fresh_vars_wrt_def, lookup_var_def]
QED
