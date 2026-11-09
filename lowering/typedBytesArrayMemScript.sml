(* Bytes1 to Bytes33 element copy in a fixed-array normalization loop. *)
Theory typedBytesArrayMem
Ancestors
  externalReturnNormalizeMem memContinuation fragExecMem fragExec exprSimAggregateChildren
  exprSimBufferStore valueCopyBytes exprSimDefs exprSimProps loweringPosts exprLoweringProps context compileEnv
  valueEncoding valueEncodingDefs valueEncodingProps vyperValue vyperTyping words arithmetic vfmConstants

Theorem typed_bytes_array_dispatch[local]:
  compile_store_memory_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) = compile_store_bytestring src dst
Proof
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem typed_bytes_array_child_run:
  compile_store_memory_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  w2n p = source_base + 64 * i /\ w2n d = dest_base + 96 * i /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  i < ncount /\ LENGTH bs <= 1 /\
  source_base + 64 * ncount <= s.vs_alloca_next /\
  dest_base + 96 * ncount <= s.vs_alloca_next /\
  (source_base + 64 * ncount <= dest_base \/
   dest_base + 96 * ncount <= source_base) /\
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV bs)
    (w2n p) s.vs_memory ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory (BaseTV (BytesT (Dynamic 33))) (BytesV bs)
        (w2n d) q.vs_memory /\
      mem_bytes_at source_base (64 * ncount) q.vs_memory =
        mem_bytes_at source_base (64 * ncount) s.vs_memory /\
      mem_bytes_at dest_base (96 * i) q.vs_memory =
        mem_bytes_at dest_base (96 * i) s.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  gnvs[typed_bytes_array_dispatch] >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    (irule buffer_bytes_header >> qexists_tac `1` >> simp[]) >>
  `32 + 32 * word_size (LENGTH bs) <= 64` by
    (`LENGTH bs = 0 \/ LENGTH bs = 1` by decide_tac >> gvs[word_size_def]) >>
  `32 + 32 * word_size (LENGTH bs) < dimword(:256)` by
    (simp[dimword_def] >> decide_tac) >>
  conj_tac
  >- (irule store_bytestring_mem_ok >>
      qexistsl_tac [`d`, `dst`, `LENGTH bs`, `p`, `src`] >>
      conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  qexists_tac `q` >> simp[] >> rpt conj_tac
  >- (irule buffer_mcopy_encoding >>
      gvs[val_footprint_def, val_wf_def, val_in_memory_def, type_memory_size_def] >>
      `LENGTH bs = 0 \/ LENGTH bs = 1` by decide_tac >> gvs[word_size_def])
  >- (irule buffer_mcopy_exterior >> decide_tac)
  >- (irule buffer_mcopy_exterior >> decide_tac) >>
  gvs[]
QED

Theorem typed_bytes_child_seq_cont:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK q /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `frag_exec_mem ctx sa sb (\u. u = s)
     (\t. t = q with vs_inst_idx := LENGTH sb.cs_current_insts) (K F)` by
    (irule frag_exec_mem_run_inst_seq >> simp[] >> metis_tac[]) >>
  drule mem_cont_sim_from_fragment >> simp[]
QED

Theorem typed_bytes_array_child_cont:
  compile_store_memory_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  w2n p = source_base + 64 * i /\ w2n d = dest_base + 96 * i /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  i < ncount /\ LENGTH bs <= 1 /\
  source_base + 64 * ncount <= s.vs_alloca_next /\
  dest_base + 96 * ncount <= s.vs_alloca_next /\
  (source_base + 64 * ncount <= dest_base \/
   dest_base + 96 * ncount <= source_base) /\
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV bs)
    (w2n p) s.vs_memory /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      val_in_memory (BaseTV (BytesT (Dynamic 33))) (BytesV bs)
        (w2n d) q.vs_memory /\
      mem_bytes_at source_base (64 * ncount) q.vs_memory =
        mem_bytes_at source_base (64 * ncount) s.vs_memory /\
      mem_bytes_at dest_base (96 * i) q.vs_memory =
        mem_bytes_at dest_base (96 * i) s.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_bytes_array_child_run >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  irule typed_bytes_child_seq_cont >> simp[] >> qexists_tac `sa` >> simp[] >>
  gnvs[typed_bytes_array_dispatch] >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `compile_store_memory ce src dst (BaseT (BytesT (Dynamic 1)))
     (BaseT (BytesT (Dynamic 1))) sa = ((),sb)` by
    simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def] >>
  drule aggregate_store_memory_straight >>
  gvs[same_blocks_def]
QED
