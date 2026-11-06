(* Annotation-capacity literal construction: reuse the general chunk proofs. *)
Theory reasonLiteralBufferPtr
Ancestors exprSimPtrLiteralBuffer exprSimPtrLiteralPayload exprSimLiteralBuffer
  exprLowering exprLoweringProps context emitHelper compileEnv freshWrites
  vfmConstants venomInst list pair

Theorem reason_literal_compiler_parts:
  compile_bytelike_literal bs ml sa = (buf,sb) ==>
  ?sm sh.
    compile_alloc_buffer (32+32*word_size ml) sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks buf.buf_operand bs 32 sh = ((),sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_bytelike_literal _ _ _ = _` mp_tac >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     GSYM word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ, pairTheory.pair_CASES]
QED

Theorem reason_literal_compiler_shape:
  compile_bytelike_literal bs ml sa = (buf,sb) ==>
  ?sm sh p.
    compile_alloc_buffer (32+32*word_size ml) sa = (buf,sm) /\
    emit_void MSTORE [Var p; Lit (n2w (LENGTH bs))] sm = ((),sh) /\
    compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
    buf.buf_operand = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    ~not_fresh_at sa p /\ not_fresh_at sm p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    emitted_insts sa sm =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p]] /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32+32*word_size ml))] [p];
       mk_inst sm.cs_next_id MSTORE [Var p; Lit (n2w (LENGTH bs))] []] ++
      emitted_insts sh sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  drule reason_literal_compiler_parts >> strip_tac >>
  drule_all literal_ptr_buffer_prefix_shape >> strip_tac >>
  `ci_mono sh sb` by
    metis_tac[ci_mono_compile_store_byte_chunks, pairTheory.SND] >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    (irule emitted_insts_append >> simp[]) >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sh ++ emitted_insts sh sb` by
    (irule emitted_insts_append >> asm_rewrite_tac[APPEND_ASSOC]) >>
  qexistsl_tac [`sm`, `sh`, `p`] >> simp[] >>
  gvs[ci_mono_def] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  decide_tac
QED
