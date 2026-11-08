(* Concrete copy witnesses, including the allocator frame. *)
Theory typedCopyAmbientEffectsPtr
Ancestors wordLoadStorePtr typedCopyPtr typedCopyLoopHeaderPtr

Theorem emit_copy_len_binop_effects_frag_ptr:
  !opc f G cx ctx PG R sa sb left right out tn s a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    emit_op opc [left;right] sa = (Var out,sb) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.emit_binop (copy_len_binop_frag_ptr, copy_len_binop_ghost_frame)
QED

Theorem emit_mload_clean_effects_frag_ptr:
  !cx ctx PG R sa sb src out G tn s a.
    emit_op MLOAD [Var src] sa = (Var out,sb) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (mload (w2n a) s) /\
      op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.emit_mload (mload_frag_ptr, mload_ghost_clean)
QED

Theorem compile_bytestring_copy_len_effects_frag_ptr:
  !cx ctx PG R sa sb src count_op G tn s a.
    compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      eval_operand count_op sf =
        SOME ((mload (w2n a) s + 31w && i2w (-32)) + 32w) /\
      op_taint tnf count_op = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.copy_len
    (emit_mload_clean_effects_frag_ptr, emit_copy_len_binop_effects_frag_ptr,
     compileEnvTheory.cs_extends_trans)
QED

Theorem compile_store_bytestring_effects_frag_ptr:
  !cx ctx PG R sa sb src dst G tn s a b len n.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len + 31) DIV 32) /\
    len + 31 < dimword (:256) /\ n < dimword (:256) /\
    mload (w2n a) s = n2w len /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
         mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.store_bytestring_with_effects true
    (compile_bytestring_copy_len_effects_frag_ptr, mcopy_operand_frag_ptr,
     mcopy_operand_ghost_frame, exprSimBufferStoreTheory.buffer_round_size,
     exprSimBufferStoreTheory.buffer_mcopy_exterior)
QED
