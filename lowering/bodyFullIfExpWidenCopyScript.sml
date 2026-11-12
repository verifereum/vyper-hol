Theory bodyFullIfExpWidenCopy
Ancestors
  bodyPtrIfExpBytesPost bodyPtrIfExpBytesSemantic bodyCopyMemory
  ptrSafetyTransport fragGasSeqPtr bodyPtrIfExpBytesCounted

Theorem inst_seq_ptr_lower_bound_transport:
  !code s G tn Gf tnf.
    inst_seq_ptr D lo0 ctx fn PG G tn code s Gf tnf /\
    lo0 <= lo /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    EVERY (\i. i.inst_opcode <> INVOKE) code ==>
    inst_seq_ptr D lo ctx fn PG G tn code s Gf tnf
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule ptr_inst_ok_lower_bound_transport >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all step_inst_allocas_from >> strip_tac >>
  first_x_assum irule >>
  gvs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Theorem compile_store_bytestring_origin_ptr_path:
  !D lo explicit ctx fn PG sa sb src dst G tn s a b len n bb.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    mload (w2n a) s = n2w len /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?Gf tnf sf.
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf) /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+n}) UNION
        {w2n b+i | i < n /\ w2n a+i IN tn.t_mem} /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_bytestring_seq_ptr >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  drule compile_store_bytestring_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sa sb)` by
    gvs[listTheory.EVERY_MEM] >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (irule inst_seq_ptr_lower_bound_transport >>
     simp[] >> qexists_tac `0` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[listTheory.EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
     gvs[listTheory.EVERY_MEM]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem compile_store_bytestring_robust_origin_ptr_path:
  !D lo explicit ctx fn PG sa sb src dst G tn s a b len n tenv sty dty stv dtv v bb.
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
      val_in_memory stv v (w2n a) m) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?Gf tnf sf.
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf) /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bodyPtrIfExpCopyHeaderTheory.robust_bytestring_header >> strip_tac >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`D`, `explicit`, `PG`] strip_assume_tac) >>
  drule_all compile_store_bytestring_robust_effects >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[]
QED
