(* Reserved-slice field stores and exterior pointer-value transport. *)
Theory logDataFieldPtr
Ancestors logValueFramePtr robustCopyTransportPtr logBytesPathPtr
  logAbiPrefixPtr logTopicScalarPtr logInstSeqPtr stmtSimLogData
  stmtSimLogDataRun stmtSimLogDataFrame bodyPtrDefs loweringPosts
  valueEncodingProps venomState finite_map words list arithmetic pred_set
  ptrDiscipline emitHelperProps venomInst exprSimBufferStore stmtSimReturn
  venomMemProofs valueEncodingProofs exprSimProps valueCopyBytes
  vyperValue vyperTyping valueEncoding

Theorem ptr_val_ok_exterior_frame:
  ptr_val_ok cx ty v op G tn s /\
  op_taint tnf op = op_taint tn op /\
  (!x. op = Var x ==> FLOOKUP Gf x = FLOOKUP G x) /\
  eval_operand op sf = eval_operand op s /\
  (!tv w. ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w ==>
    val_wf tv v /\
    !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN writes) /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) ==>
  ptr_val_ok cx ty v op Gf tnf sf
Proof
  strip_tac >> simp[ptr_val_ok_def] >>
  (conj_tac >- gvs[ptr_val_ok_def]) >> strip_tac >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  `val_wf tv v /\
   (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN writes)` by
    metis_tac[] >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
   (val_footprint tv v <> 0 ==>
    ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + val_store_size tv v <= b+sz)` by
    (gvs[ptr_val_ok_def,ptr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`s.vs_memory`,`sf.vs_memory`,`tn.t_mem`,`tnf.t_mem`,`writes`] >> simp[]) >>
  metis_tac[]
QED

Theorem log_data_address_seq_ptr:
  emit_op ADD [Var buf; Lit (n2w off)] sa = (Var out,sb) /\
  ptr_covers G tn buf s cap /\ lookup_var buf s = SOME (n2w b) /\
  off+n <= cap /\ b+cap < dimword(:256) /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    lookup_var out sf = SOME (n2w (b+off)) /\
    FLOOKUP Gf out = FLOOKUP G buf /\ ptr_covers Gf tnf out sf n /\
    op_taint tnf (Var out) = {} /\ sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ptr_covers G tn buf s (off+n)` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_MONO_ADD_EQ]) >>
  `b < dimword(:256) /\ b+off < dimword(:256)` by decide_tac >>
  `w2n ((n2w b):256 word) + off < dimword(:256)` by simp[] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `tnf.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[word_add_n2w]
QED

Theorem log_data_word_store_seq_ptr:
  emit_void MSTORE [Var dst;src] sa = ((),sb) /\
  ptr_covers G tn dst s 32 /\ op_taint tn src = {} /\
  lookup_var dst s = SOME a /\ eval_operand src s = SOME w /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ w = typed_val_to_w256 tv v /\
  ~ctx_has_dalloca ctx ==>
  ?tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tnf /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
    (!i. ~(w2n a <= i /\ i < w2n a+32) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. lookup_var p sf = lookup_var p s /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    log_write_frame sa (w2n a) 32 s sf
Proof
  strip_tac >> drule_all emit_mstore_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `eval_operand (Var dst) s = SOME a` by simp[eval_operand_def] >>
  drule_all buffer_store_word_encoding >> strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_type_sizes] >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def]) >>
  `tnf.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qexistsl_tac [`tnf`,`sf`] >> gvs[] >>
  conj_tac >- suspend "word_robust" >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  (conj_tac >- simp[op_taint_def,lookup_var_def,mstore_def,write_memory_with_expansion_def]) >>
  simp[log_write_frame_def,lookup_var_def,mstore_def,write_memory_with_expansion_def] >>
  qpat_x_assum `!a k. _` mp_tac >>
  simp[mstore_def,write_memory_with_expansion_def]
QED
Resume log_data_word_store_seq_ptr[word_robust]:
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_agree_outside _ mem0 m` >>
  irule val_in_memory_mem_agree >> (conj_tac >- simp[]) >>
  qexistsl_tac [`32`,`mem0`] >> simp[Abbr `mem0`] >>
  irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
  qpat_x_assum `mem_agree_outside _ _ m` mp_tac >>
  simp[mem_agree_outside_def] >>
  disch_then (qspec_then `w2n a+x` mp_tac) >>
  simp[LIST_EQ_REWRITE,EL_mem_bytes_at]
QED
Finalise log_data_word_store_seq_ptr

Theorem log_data_bytes_size:
  supported_scalar_type ty /\ is_bytestring_type ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v ==>
  ?len.
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_bytes cenv ty
Proof
  strip_tac >>
  `val_store_size tv v <= type_memory_bytes cenv ty` by
    metis_tac[val_store_size_le,log_scalar_memory_size] >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >>
  gvs[value_has_type_def,val_store_size_def,vfmConstantsTheory.word_size_def]
QED

Theorem ptr_val_ok_store_covers:
  ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand op s = SOME w /\
  val_footprint tv v <> 0 /\ n <= val_store_size tv v ==>
  ?p. op = Var p /\ ptr_covers G tn p s n
Proof
  strip_tac >> fs[ptr_val_ok_def,ptr_mem_ok_def] >>
  `?p b sz. op = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b+sz` by metis_tac[] >>
  gvs[] >> simp[ptr_covers_def] >>
  qexists_tac `w` >> gvs[eval_operand_def] >> decide_tac
QED
