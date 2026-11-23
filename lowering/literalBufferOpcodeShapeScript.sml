(* Opcode check for the newly emitted suffix, independent of the old block. *)
Theory literalBufferOpcodeShape
Ancestors
  exprLoweringProps emitHelperProps exprLowering context emitHelper compileEnv
  venomInst vfmConstants words list rich_list

Theorem literal_chunks_non_dalloca[local]:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((),sb) ==>
    ?tail. sb.cs_current_insts = sa.cs_current_insts ++ tail /\
           EVERY (\i. i.inst_opcode <> DALLOCA /\ ~MEM i.inst_opcode [CREATE;CREATE2]) tail
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- (rpt gen_tac >> simp[compile_store_byte_chunks_def, comp_return_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  fs[mk_inst_def]
QED

Theorem literal_bytelike_emitted_admin:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA /\ ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sa sb)
Proof
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_bytelike_literal_def, LET_THM, comp_bind_def,
     comp_ignore_bind_def, GSYM word_size_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `emit_void MSTORE [buf.buf_operand; Lit (n2w (LENGTH bs))] sm = (u,sh)` >>
  Cases_on `u` >>
  rename1 `compile_store_byte_chunks buf.buf_operand bs 32 sh = (v,sb)` >>
  Cases_on `v` >>
  drule literal_chunks_non_dalloca >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  asm_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem literal_bytelike_emitted_non_dalloca:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  strip_tac >> drule literal_bytelike_emitted_admin >> simp[EVERY_MEM]
QED
