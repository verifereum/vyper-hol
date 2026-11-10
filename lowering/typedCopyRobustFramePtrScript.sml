(* Robust bytestring normalization and ambient effects, on one witness. *)
Theory typedCopyRobustFramePtr
Ancestors typedCopyAmbientFramePtr typedCopyRobustTransportPtr
  typedCopyBytesRobustPtr

Theorem compile_store_bytestring_robust_ambient_frag_ptr:
  !cx ctx PG R sa sb src dst G tn s a b len n tenv sty dty stv dtv v.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory stv v (w2n a) m) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tnf sf) /\
      (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!ft fv p. val_wf ft fv /\
        (p + type_memory_size ft <= w2n b \/ w2n b+n <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m)
Proof
  typedCopyRobustLib.intro >>
  typedCopyRobustLib.execute
    (compile_store_bytestring_ambient_frag_ptr,
     robust_representation_exterior_frame) >>
  `stor_taint_ok cx tn s ==> stor_taint_ok cx tnf sf` by
    simp[bodyPtrDefsTheory.stor_taint_ok_def] >>
  typedCopyRobustLib.witness >>
  typedCopyRobustLib.conclude clean_copied_window
QED
