(* Robust copy results for a witnessed checked instruction sequence. *)
Theory logBytesRobustSeqPtr
Ancestors logBytesSeqPtr typedCopyBytesRobustPtr typedCopyRobustTransportPtr
  representationCleanPtr robustCopyTransportPtr valueCopyBytes valueEncodingProps
  loweringPosts exprSimDefs exprSimProps venomMemProofs bodyPtrDefs
  valueEncodingProofs exprSimBufferStore list arithmetic

val _ = load "typedCopyRobustLib";

Theorem compile_store_bytestring_robust_seq_ptr:
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
    val_in_memory stv v (w2n a) m) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!ft fv p. val_wf ft fv /\
      (p+type_memory_size ft <= w2n b \/ w2n b+n <= p) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m)
Proof
  disch_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
   (!i. w2n a+32 <= i /\ i < w2n a+32+len ==> i NOTIN tn.t_mem)` by
    typedCopyRobustLib.source >>
  qpat_x_assum `_ /\ _` strip_assume_tac >>
  drule_all compile_store_bytestring_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac)))) >>
  drule robust_representation_exterior_frame >> disch_then drule >>
  disch_then (assume_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[] >>
  (conj_tac >- typedCopyRobustLib.destination clean_copied_window) >>
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!ft fv p m. _` irule >> asm_rewrite_tac[]
QED
