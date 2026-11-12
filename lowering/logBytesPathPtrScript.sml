(* Counted execution of the robust bytestring store; sf retains the raw
   instruction-sequence cursor, while the path endpoint advances it. *)
Theory logBytesPathPtr
Ancestors logBytesRobustSeqPtr logBytesCodePtr fragGasSeqPtr
  venomInst venomState list rich_list

Theorem compile_store_bytestring_robust_path_ptr:
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
    val_in_memory stv v (w2n a) m) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
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
  mp_tac compile_store_bytestring_robust_seq_ptr >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  strip_tac >> qpat_x_assum `_ /\ _` strip_assume_tac >>
  drule compile_store_bytestring_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL,EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[] >> gvs[]
QED
