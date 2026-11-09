(* Complete ambient projections on the concrete copy-prefix witnesses. *)
Theory typedCopyAmbientFramePtr
Ancestors typedCopyAmbientEffectsPtr typedCopyPtr typedCopyLoopHeaderPtr

Theorem emit_copy_len_binop_ambient_frag_ptr:
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
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_copy_len_binop_effects_frag_ptr >>
  metis_tac[]
QED

Theorem emit_mload_clean_ambient_frag_ptr:
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
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >> drule_all emit_mload_clean_effects_frag_ptr >>
  metis_tac[]
QED

Theorem compile_bytestring_copy_len_ambient_frag_ptr:
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
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt strip_tac >> drule_all compile_bytestring_copy_len_effects_frag_ptr >>
  metis_tac[]
QED

Theorem compile_store_bytestring_ambient_frag_ptr:
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
  rpt strip_tac >> drule_all compile_store_bytestring_effects_frag_ptr >>
  metis_tac[]
QED

Theorem typed_copy_loop_address_ambient_frag_ptr:
  !cx ctx PG R sb si ctr so doff sp dp sr dr id i ss ds a b S T G tn s.
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    i*ss < S /\ i*ss+ss <= S /\ i*ds < T /\ i*ds+ds <= T /\
    w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) /\
    si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
    si.cs_current_insts = sb.cs_current_insts ++
      [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
       mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
       mk_inst (id+2) ADD [Var sr;Var so] [sp];
       mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sb si
        (\g t v. g=G /\ t=tn /\ v=s)
        (\g t v. g=Gf /\ t=tnf /\ v=sf) R /\
      lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
      lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
      ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
      sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
      tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. ~MEM p [so;doff;sp;dp] ==>
        lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
        op_taint tnf (Var p)=op_taint tn (Var p))
Proof
  typedCopyLoopAmbientLib.address_witnesses >>
  conj_tac >- (typedCopyLoopAmbientLib.address_fragment typed_copy_loop_mul_frag_ptr) >>
  typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers
QED

(* Header entry/exit and backedge use this same explicit two-scalar update.
   Their execution theorems already expose the state and taint expressions,
   so no existential projection is discarded at these boundaries. *)
Theorem typed_copy_loop_control_ambient_frame:
  !tn s p q a b lbl.
    (tn with t_var := (tn.t_var |+ (p,{})) |+ (q,{})).t_imm = tn.t_imm /\
    (jump_to lbl (update_var q b (update_var p a s))).vs_call_ctx = s.vs_call_ctx /\
    (jump_to lbl (update_var q b (update_var p a s))).vs_accounts = s.vs_accounts /\
    (jump_to lbl (update_var q b (update_var p a s))).vs_transient = s.vs_transient
Proof
  simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def]
QED
